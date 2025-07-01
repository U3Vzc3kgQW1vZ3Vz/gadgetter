//Detection of frame entry points
package jdd.tranModel.Rules;
import jdd.PointToAnalyze.pointer.Pointer;
import jdd.tranModel.Rule;
import jdd.tranModel.Taint.Taint;
import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.container.FieldsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import lombok.extern.slf4j.Slf4j;
import jdd.markers.Stage;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;
import jdd.util.ClassRelationshipUtils;
import callgraph.utilClass.StaticAnalyzeUtils.FieldUtil;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;

import java.util.HashSet;
import java.util.LinkedList;

@Slf4j
public class TaintGenerateRule implements Rule {
    public static boolean fieldGenerate = false;

    public HashSet<String> readObjectSigs = new HashSet<>();
    public HashSet<String> getFieldsFromInputSigs = new HashSet<>();

    public TaintGenerateRule(){
        readObjectSigs = ClassRelationshipUtils.getAllSubMethodSigs("<java.io.ObjectInput: java.lang.Object readObject()>");
        getFieldsFromInputSigs.addAll(ClassRelationshipUtils.getAllSubMethodSigs("<java.io.ObjectInputStream$GetField: java.lang.Object get(java.lang.String,java.lang.Object)>"));
        for (String tmpMtdSig: getFieldsFromInputSigs){
            if (!Scene.v().containsMethod(tmpMtdSig))
                continue;
            SootMethod tmpMtd = Scene.v().getMethod(tmpMtdSig);
            SootClass tmpSootClass = tmpMtd.getDeclaringClass();
            for (SootMethod tmpMtdIn: tmpSootClass.getMethods()){
                BasicDataContainer.blackList.add(tmpMtdIn.getSignature());
            }
        }
    }
    /**
     * Use field/ObjectInputStream as a blemish source
     * @param transformable
     * @param descriptor
     */
    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {

        TransformableNode tfNode = (TransformableNode) transformable;

Unit currentUnit = tfNode.node.unit; // Considering that some methods deal with Stmt's parent class Unit, this step is done to avoid errors
        Stmt currentStmt = (Stmt) currentUnit;

// Process assignment statements
// Step

        if (currentStmt instanceof AssignStmt) {
            Value left = ((AssignStmt) currentStmt).getLeftOp();
            Value right = ((AssignStmt) currentStmt).getRightOp();

// 1. When calling the method: (a) Processing of methods that cannot be tracked; (b) Stainless treatment of related methods such as readObject
            if (currentStmt.containsInvokeExpr()){
                SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();
// TODO: (a) Don't deal with it first, observe whether the problem still exists

boolean generateFlag = false; // Identifier for determining whether the taint can be generated
                ValueBox thisValueBox = Parameter.getThisValueBox(currentStmt);
                if (thisValueBox != null){
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(thisValueBox.getValue())){
                        if (taint.accessPath.isEmpty()){
                            generateFlag = true;
                            break;
                        }
                    }
                }

                if (generateFlag){
                    Taint newTaint = descriptor.getOrCreateTaint(left, new LinkedList<>());
                    RuleUtils.addTaint(descriptor, newTaint);

// (b-1) Object read for ObjectInput.readObject()
// (b-2) ObjectInputStream.GetField.get("fieldName",), obtain the field name according to the first parameter, and then remove the corresponding SootField
// Find from FieldsContainer (based on global information)
                    if (readObjectSigs.contains(invokedMethod.getSignature())) {
if (BasicDataContainer.infosCollect) { // TODO: If not found, try to match according to the type
// TODO: Go to FieldsContainer.fieldRefValuesMap to find
                            SootField sootField = FieldsContainer.getSootFieldRefByStream(left, descriptor.sootMethod);
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, null, descriptor);
                            if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER)){
                                descriptor.sourcesTaintGraph.sourceUnFound.put(
                                        ((AssignStmt) currentStmt).getLeftOpBox(), tfNode
                                );
                            }
// SourceNode newSourceNode = RuleUtils.createSourceNode(sootField, newTaint);
// descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode, left);
                        }
                    }else if (getFieldsFromInputSigs.contains(invokedMethod.getSignature())){
                        SootClass sootClass = descriptor.getCurrentClass();
                        SootField sootField = null;

                        Value fieldNameValue = currentStmt.getInvokeExpr().getArg(0);
                        if (sootClass != null & fieldNameValue instanceof Constant){
                            sootField = FieldUtil.getSootFieldByName(sootClass, fieldNameValue);
                            RuleUtils.createAndAddSourceNode(sootField, newTaint, null, descriptor);
                        }
                    }
                }

            }
            else if (right instanceof FieldRef){
                boolean generateFlag = false;
                if (descriptor.paramIdMapLocalValue.containsKey(-1)){
                    for (Taint taint: descriptor.getAllTaintsAboutThisValue(descriptor.paramIdMapLocalValue.get(-1))){
                        if (taint.accessPath.isEmpty()) {
                            generateFlag = true;
                            break;
                        }
                    }
                }

                if (generateFlag) {
                    if (right instanceof JInstanceFieldRef) {
                        SootField sootField = ((FieldRef) right).getField();
                        Value basedObj = ((JInstanceFieldRef) right).getBase();
// If basedObj is not this, perform field.field search
                        LinkedList<SootField> accessPath = new LinkedList<>();
                        if (BasicDataContainer.stage.equals(Stage.IOCD_GENERATING)
                                | BasicDataContainer.stage.equals(Stage.IOCD_SUPPLEMENT_INFER))
                            accessPath = RuleUtils.getAccessPath(basedObj, sootField, descriptor);

                        Taint newTaint = descriptor.getOrCreateTaint(left, accessPath);
                        RuleUtils.addTaint(descriptor, newTaint);

                        Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
                        descriptor.pointTable.setPointer( newTaint, pointer);

                        if (BasicDataContainer.infosCollect) {
                            RuleUtils.createAndAddSourceNode(sootField, newTaint,
                                    ((JInstanceFieldRef) right).getBase(), descriptor);
// SourceNode newSourceNode = RuleUtils.createSourceNode(sootField, newTaint);
// descriptor.sourcesTaintGraph.addTaintedSourceNode(newSourceNode,left);
                        }
                    }
// 3. Other situations, including static fields, do not directly generate taints (static fields cannot be controlled during deserialization)
                    else if (right instanceof StaticFieldRef){
                        SootField sootField = ((StaticFieldRef) right).getField();
                        Value recordedValue = FieldsContainer.getStaticSootFieldInfo(sootField, descriptor.getCurrentClass());
                        if (recordedValue != null){
// Static fields only record the situation where they are constants, because if they are variables, the attacker cannot control them.
                            if (recordedValue instanceof Constant){
                                SourceNode sourceNode = new SourceNode(recordedValue);
// sourceNode.constant = recordedValue;
                                descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode,left);
                            }
                        }
                    }
                    else {
log.info("--- FieldRef in TaintGenerateRule: "+ right);
                    }
                }
            }
        }

        if (BasicDataContainer.infosCollect & descriptor.isEntry){
            if (currentStmt instanceof IdentityStmt){
                IdentityStmt identityStmt = (IdentityStmt) currentStmt;
                Value left = identityStmt.getLeftOp();
                Value right = identityStmt.getRightOp();

                if (right instanceof ParameterRef){
                    int ind = ((ParameterRef) right).getIndex();
                    SourceNode sourceNode = new SourceNode(ind, descriptor.sourcesTaintGraph.entryMethod);
                    descriptor.sourcesTaintGraph.addTaintedSourceNode(sourceNode,left);
                }
            }
        }
    }
}
