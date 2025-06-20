package jdd.tranModel.Rules;

import jdd.PointToAnalyze.pointer.Pointer;
import soot.*;
import jdd.tranModel.Rule;
import jdd.tranModel.Taint.Taint;
import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import lombok.extern.slf4j.Slf4j;
import jdd.rules.sinks.FileCheckRule;
import soot.jimple.*;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNewArrayExpr;
import jdd.util.ClassRelationshipUtils;
import java.util.StaticAnalyzeUtils.FieldUtil;
import java.util.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.util.*;

@Slf4j
public class TaintSpreadRule implements Rule {
    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {
        TransformableNode transformableNode = (TransformableNode) transformable;
        Stmt stmt = (Stmt) transformableNode.node.unit;

// 1. Assign
        if (stmt instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) stmt;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

// (1-1) If it is Array type, the pollution of the first element is not considered
            if (left instanceof JArrayRef)
                left = ((JArrayRef) left).getBase();
            if (right instanceof JArrayRef) {
                right = ((JArrayRef) right).getBase();
            }


            if (Utils.isTainted(left,descriptor.taints) & Utils.isTainted(right,descriptor.taints)){
                descriptor.sourcesTaintGraph.recordSourceInfluence(left, right);
            }


            if (right instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) right;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();
// Match all possible taints and consider fields sensitivity to generate new taints for left
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(object)){
                    LinkedList<SootField> tryMatch = taint.match(object,sootField);
                    if (tryMatch != null){
                        Taint newTaint = descriptor.getOrCreateTaint(left,tryMatch);
                        RuleUtils.addTaint(descriptor, newTaint);
                        if (BasicDataContainer.infosCollect){
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, object, descriptor);
                        }
                    }
                }
            }
            else if (left instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) left;
                Value object = jInstanceFieldRef.getBase();
                SootField field = jInstanceFieldRef.getField();

                for (Taint taint: descriptor.getAllTaintsAboutThisValue(right)){
                    LinkedList<SootField> accessPath = new LinkedList<>();
// For some internal class methods, a variable will be passed in and assigned to this. At this time, fields sensitive information is not recorded (in order to provide conditions for generating field.field when generating)
                    if (!field.getName().equals("this$0"))
                        accessPath.add(field);

                    accessPath.addAll(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(object,accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);
                    if (BasicDataContainer.infosCollect){
                        if (!RuleUtils.isInitMtdTaintSourceRecord(field, right, descriptor))
                            descriptor.sourcesTaintGraph.recordSourceInfluence(left, right);
                    }
                }
            }
else if (right instanceof CastExpr){ // cast type conversion
Value object = ((CastExpr) right).getOp(); // Take the object cast and perform stain matching

                for (Taint taint: descriptor.getAllTaintsAboutThisValue(object)){
                    Taint newTaint = descriptor.getOrCreateTaint(left, new LinkedList<>(taint.accessPath));
                    RuleUtils.addTaint(descriptor,newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, object);
                    }
                }
            }
// else if (right instanceof NewArrayExpr){
// // TODO: For array type, do you need to record the association of size? How to record it more appropriate?
// }
            else if (right instanceof BinopExpr){
                for (ValueBox opValueBox: ((BinopExpr) right).getUseBoxes()){
                    if (opValueBox == null)
                        continue;
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(opValueBox.getValue())) {
                        LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                        Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                        RuleUtils.addTaint(descriptor, newTaint);

                        if (BasicDataContainer.infosCollect)
                            descriptor.sourcesTaintGraph.addTaintedSourceNode(left, opValueBox.getValue());
                    }
                }
            }
            else if (right instanceof LengthExpr){
                Value arrayValue = ((LengthExpr) right).getOp();
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(arrayValue)){
                    LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, right);
                    }
                }
            }
// For constants, record sources, do not record as taint
            else if (right instanceof Constant){
                if (BasicDataContainer.infosCollect) {
                    SourceNode newSourceNode = new SourceNode(right);
                    descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, left);
                }
            }
// Do not record stains, only source
            else if (right instanceof JNewArrayExpr){
                Value sizeValue = ((JNewArrayExpr) right).getSize();
                descriptor.sourcesTaintGraph.addTaintedSourceNode(left, sizeValue);
            }
            else {
// Direct equality
                for (Taint taint: descriptor.getAllTaintsAboutThisValue(right)){
                    LinkedList<SootField> accessPath = new LinkedList<>(taint.accessPath);
                    Taint newTaint = descriptor.getOrCreateTaint(left,accessPath);
                    RuleUtils.addTaint(descriptor, newTaint);

                    if (BasicDataContainer.infosCollect){
                        descriptor.sourcesTaintGraph.addTaintedSourceNode(left, right);
                    }
                }
            }
        }

// 2. Return, record the returned stain
        if (stmt instanceof ReturnStmt){
            for (ValueBox valueBox : stmt.getUseBoxes()) {
                descriptor.retTainted.addAll(descriptor.getAllTaintsAboutThisValue(valueBox.getValue()));
            }
            descriptor.returnStmt = (ReturnStmt) stmt;
        }

// 3. (a = ) f(taint,...)
        if (stmt.containsInvokeExpr()){
            InvokeExpr invokeExpr = stmt.getInvokeExpr();
            SootMethod invokedMethod = invokeExpr.getMethod();
            RuleUtils.applySpreadRules(descriptor, stmt);
// Processing of File
            if (FileCheckRule.fileClassNames.contains(invokedMethod.getDeclaringClass().getName())){
                if (invokeExpr.getMethod().getName().equals("<init>")){
                    ValueBox pathValueBox = Parameter.getArgByType(invokeExpr, "java.lang.String");
                    ValueBox fileValueBox = Parameter.getArgByType(invokeExpr, "java.io.File");
                    ValueBox thisValueBox = Parameter.getThisValueBox(transformableNode.node);
                    if (pathValueBox != null & fileValueBox == null & thisValueBox != null){
                        if (Utils.isTainted(pathValueBox.getValue(), descriptor.taints)){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), pathValueBox.getValue());
                            }
                        }
                    }
                    else if (pathValueBox == null & fileValueBox != null & thisValueBox != null){
                        if (Utils.isTainted(fileValueBox.getValue(), descriptor.taints)){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), fileValueBox.getValue());
                            }
                        }
                    }
                    else if (pathValueBox != null & fileValueBox != null & thisValueBox != null){
                        Value arg0 = invokeExpr.getArg(0);
                        if (Utils.isTainted(arg0, descriptor.taints)
                                & (arg0.equals(pathValueBox.getValue()) | arg0.equals(fileValueBox.getValue()))){
                            RuleUtils.addTaint(thisValueBox.getValue(), new LinkedList<>(), descriptor);

                            if (BasicDataContainer.infosCollect){
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(thisValueBox.getValue(), arg0);
                            }
                        }
                    }
                }
            }

// Special processing of entrySet() of Map
// <java.util.Map: java.util.Set entrySet()>
            if (invokedMethod.getSubSignature().equals("java.util.Set entrySet()")){
                ValueBox thisValueBox = Parameter.getThisValueBox(transformableNode.node);
                Value retValue = Parameter.getReturnedValue(transformableNode.node);
                if (thisValueBox != null & retValue != null){
                    HashSet<SourceNode> taitSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue());
                    if (!taitSourceNodes.isEmpty())
                        descriptor.sourcesTaintGraph.createAndAddSourceNode(thisValueBox.getValue(), retValue, false, true);
                    else {
// Heuristic Matching
                        SootClass sootClass = null;
                        Pointer pointer = descriptor.pointTable.getPointer(thisValueBox.getValue());
                        if (thisValueBox.getValue().equals(descriptor.paramIdMapLocalValue.get(-1))){
                            sootClass = descriptor.getCurrentClass();
                        }
                        else if (pointer != null){
                            sootClass = Utils.toSootClass(pointer.getType());
                        }else {
                            sootClass = Utils.toSootClass(thisValueBox.getValue().getType());
                        }
                        if (sootClass != null) {
                            for (SootField sootField : FieldUtil.getAllDeclaredFields(sootClass)) {
                                if (!sootField.getType().toString().endsWith("[]"))
                                    continue;

                                SootClass classOfArrayElement = Utils.toSootClass(sootField.getType());
                                if (ClassRelationshipUtils.isSubClassOf(classOfArrayElement, BasicDataContainer.commonClassMap.get("Entry"))){
                                    SourceNode newSourceNode = SourceNode.createFieldSourceNode(sootField, sootClass);
                                    descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, retValue);
                                    break;
                                }
                            }
                        }
                    }
                }
            }

// Record temporary created objects: There is no need to check whether they can be serialized, because they are automatically generated dynamically during program execution.
            if (invokedMethod.getName().equals("getInstance") & invokedMethod.isStatic()){
                Value retValue = Parameter.getReturnedValue(stmt);
                if (retValue != null)
                    descriptor.tempGeneratedObjs.add(retValue);
            }
        }
    }
}
