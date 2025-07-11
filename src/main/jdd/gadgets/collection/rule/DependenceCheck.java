package jdd.gadgets.collection.rule;

import soot.*;
import jdd.tranModel.Rules.RuleUtils;
import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import jdd.gadgets.collection.node.ConditionUtils;
import jdd.gadgets.collection.node.DependenceNode;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.collection.markers.DependenceType;
import jdd.markers.Stage;
import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;
import soot.tagkit.Tag;
import jdd.util.ClassRelationshipUtils;
import callgraph.utilClass.StaticAnalyzeUtils.FieldUtil;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.util.*;

import java.io.IOException;

import static jdd.util.ClassRelationshipUtils.isSubClassOf;

public class DependenceCheck implements InferRule {
    @Override
    public void apply(MethodDescriptor descriptor,
                      GadgetInfoRecord gadgetInfosRecord,
                      Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        Stmt stmt = (Stmt) tfNode.node.unit;

        if (stmt instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) stmt;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

            if (left instanceof ArrayRef)
                left = ((ArrayRef) left).getBase();
            if (right instanceof ArrayRef)
                right = ((ArrayRef) right).getBase();

            checkAssignDependence(tfNode, left, right, descriptor, gadgetInfosRecord);
        }
        else if (stmt.containsInvokeExpr()){
            identifyReflectionDependenceForResolve(descriptor,tfNode,gadgetInfosRecord);
        }
    }


    public static void checkAssignDependence(TransformableNode tfNode,
                                                 Value left, Value right,
                                                 MethodDescriptor descriptor,
                                                 GadgetInfoRecord gadgetInfoRecord){
// HashSet<SourceNode> rightSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(right);
        HashSet<SourceNode> rightSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(right, gadgetInfoRecord, descriptor);

        if (left instanceof JInstanceFieldRef){
            if (!Utils.isTainted(right, descriptor.taints) & (left.getType().toString().contains("[]"))){
                SourceNode leftSourceNode = SourceNode.createFieldSourceNode(((JInstanceFieldRef) left).getField(), descriptor.getCurrentClass());
                for (SourceNode sizeSourceNode: RuleUtils.getTaintedFieldSourcesViaAF(right, gadgetInfoRecord, descriptor)) {
                    if (sizeSourceNode.getType().toString().equals("int") | sizeSourceNode.getType().toString().equals("java.lang.Integer")) {
                        DependenceNode dependenceNode = new DependenceNode(leftSourceNode, sizeSourceNode, DependenceType.ARRAY_SIZE);
                        gadgetInfoRecord.addDependenceNode(dependenceNode, true);
                    }
                }
                return;
            }

// TODO: Will fields need to be considered? JDD will not deal with it for the time being
            SootField sootField = ((JInstanceFieldRef) left).getField();
            LinkedList<SootField> fields = new LinkedList<>();
            fields.add(sootField);
            SourceNode leftSourceNode = new SourceNode(fields, descriptor.getCurrentClass());

// TODO: The direct impact relationship record of any type is currently strictly restricted, considering the value of the transient field to the relationship of the fei transient field during the writeObject process
            if (BasicDataContainer.stage == Stage.IOCD_SUPPLEMENT_INFER) {
                if (!FieldUtil.isTransientType(left)) {
                    for (SourceNode rightSourceNode : rightSourceNodes) {
                        if (!rightSourceNode.isField())
                            continue;
                        DependenceNode dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.ASSIGNED);
                        gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                    }
                }
            }

            if (!Utils.isTainted(((JInstanceFieldRef)left).getBase(), descriptor.taints) | !Utils.isTainted(right, descriptor.taints))
                return;

            identifyReflectionDependence(left.getType(), right.getType(), leftSourceNode, rightSourceNodes, gadgetInfoRecord);
            if (left.getType().toString().contains("[]") & right.getType().toString().contains("[]")) {
                for (SourceNode rightSourceNode: rightSourceNodes) {
                    if (rightSourceNode.getType().toString().equals("int") | rightSourceNode.getType().toString().equals("java.lang.Integer")) {
                        DependenceNode dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.ARRAY_SIZE);
                        gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                    }
                }
            }
            if (isSubClassOf(Utils.toSootClass(left.getType()), BasicDataContainer.commonClassMap.get("Map"))
                    | isSubClassOf(Utils.toSootClass(left.getType()), BasicDataContainer.commonClassMap.get("List"))){
// TODO: Adding MAP/LIST and other element types to identify
                Tag signatureTag = sootField.getTag("SignatureTag");
                if (signatureTag != null) {
                    LinkedList<String> extractedTypes = Utils.extractArrayElementType(signatureTag.toString());
                    for (String typeString: extractedTypes){
                        if (typeString.contains("java.lang.reflect.Method") & right.getType().toString().equals("java.lang.reflect.Method")){
                            for (SourceNode rightSourceNode : rightSourceNodes) {
                                if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                                    DependenceNode dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_METHOD);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                } else if (rightSourceNode.getType().toString().equals("java.lang.String")) {
                                    DependenceNode dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.METHOD_NAME);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                }
                            }
                        }
                        if (typeString.contains("java.lang.Class") & right.getType().toString().equals("java.lang.Class")){
                            for (SourceNode rightSourceNode : rightSourceNodes) {
                                if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")) {
                                    DependenceNode dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_METHOD);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                } else if (rightSourceNode.getType().toString().equals("java.lang.String")) {
                                    DependenceNode dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_NAME);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                }
                            }
                        }
                        if (typeString.contains("java.lang.String") & right.getType().toString().equals("java.lang.String")){
                            for (SourceNode rightSourceNode : rightSourceNodes) {
                                if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")) {
                                    DependenceNode dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.METHOD_NAME);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                } else if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                                    DependenceNode dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_NAME);
                                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                                }
                            }
                        }
                    }
                }
            }
        }

        if (tfNode.containsInvoke()){
            InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
            String invokedMethodSig = invokeExpr.getMethod().getSignature();
            if (ConditionUtils.compareMethodsMapInputArg.containsKey(invokedMethodSig)) {
                Value comparedValue = invokeExpr.getArg(ConditionUtils.compareMethodsMapInputArg.get(invokedMethodSig).getValue());
                Value compareValue = RuleUtils.getValueByParamIndex(
                        (Stmt) tfNode.node.unit, ConditionUtils.compareMethodsMapInputArg.get(invokedMethodSig).getKey());
                if (Utils.isTainted(comparedValue, descriptor.taints) & Utils.isTainted(compareValue, descriptor.taints)){
// HashSet<SourceNode> comparedSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(comparedValue);
// HashSet<SourceNode> compareSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(compareValue);
                    HashSet<SourceNode> comparedSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(comparedValue,gadgetInfoRecord,descriptor);
                    HashSet<SourceNode> compareSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(compareValue,gadgetInfoRecord,descriptor);

                    for (SourceNode tmpCompareSourceNode: compareSourceNodes) {
                        for (SourceNode tmpComparedSourceNode : comparedSourceNodes) {
                            identifyReflectionDependence(
                                    tmpCompareSourceNode.getType(), tmpComparedSourceNode.getType()
                                    , tmpCompareSourceNode, comparedSourceNodes, gadgetInfoRecord);
                        }
                    }
                }
            }

            if (ConditionUtils.mapElementSigs.contains(invokeExpr.getMethod().getSignature())) {
                ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
                ValueBox argValueBox = Parameter.getArgValueBox(tfNode.node, 0);
                if (thisValueBox != null & argValueBox != null) {
                    if (!descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue()).isEmpty()
                            & Utils.isTainted(argValueBox.getValue(), descriptor.taints)) {
// HashSet<SourceNode> thisSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue());
// HashSet<SourceNode> argSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(argValueBox.getValue());
                        HashSet<SourceNode> thisSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(thisValueBox.getValue(), gadgetInfoRecord, descriptor);
                        HashSet<SourceNode> argSourceNodes = RuleUtils.getTaintedFieldSourcesViaAF(argValueBox.getValue(), gadgetInfoRecord, descriptor);
                        for (SourceNode argSourceNode: argSourceNodes){
                            if (!argSourceNode.isField())
                                continue;
                            for (SourceNode thisSourceNode: thisSourceNodes){
                                if (!thisSourceNode.isField())
                                    continue;

                                DependenceNode dependenceNode = new DependenceNode(thisSourceNode, argSourceNode,
                                        DependenceType.ARRAY_ELEMENT, invokeExpr.getMethod().getName());
                                gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                            }
                        }
                    }
                }
            }
            identifyReflectionDependenceForResolve(descriptor,tfNode,gadgetInfoRecord);
        }
    }
// Change it to incoming parameter setting emmm <init is also good>
    public static void identifyReflectionDependenceForResolve(MethodDescriptor descriptor,
                                                              TransformableNode tfNode,
                                                              GadgetInfoRecord gadgetInfoRecord){
        if (!tfNode.containsInvoke() || tfNode.getUnitInvokeExpr().getArgCount() != 2)
            return;
        if (!descriptor.sourcesTaintGraph.entryMethod.getSubSignature().equals("java.lang.Object readResolve()"))
            return;

        ValueBox retValueBox = Parameter.getReturnedValueBox(tfNode.node);
        if (retValueBox == null)
            return;
        Value arg0 = tfNode.getUnitInvokeExpr().getArg(0);
        Value arg1 = tfNode.getUnitInvokeExpr().getArg(1);

        Type retType = retValueBox.getValue().getType();
        Type arg0Type = arg0.getType();
        Type arg1Type = arg1.getType();

        int typeCode = RuleUtils.turnTypeToInt(retType) ^ RuleUtils.turnTypeToInt(arg0Type) ^ RuleUtils.turnTypeToInt(arg1Type);
        if (typeCode != 14)
            return ;

        HashSet<SourceNode> retSourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(retValueBox.getValue());
        HashSet<SourceNode> arg0SourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(arg0);
        HashSet<SourceNode> arg1SourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(arg1);

        for (SourceNode sourceNode1: retSourceNodes){
            if (!sourceNode1.isField())
                continue;
            for (SourceNode sourceNode2: arg0SourceNodes){
                if (!sourceNode2.isField())
                    continue;

                identifyReflectionDependence(sourceNode1.getType(), sourceNode2.getType(), sourceNode1, arg0SourceNodes, gadgetInfoRecord);
            }

            for (SourceNode sourceNode2: arg1SourceNodes){
                if (!sourceNode2.isField())
                    continue;

                identifyReflectionDependence(sourceNode1.getType(), sourceNode2.getType(), sourceNode1, arg1SourceNodes, gadgetInfoRecord);
            }
        }
        for (SourceNode sourceNode1: arg0SourceNodes){
            if (!sourceNode1.isField())
                continue;

            for (SourceNode sourceNode2: arg1SourceNodes){
                if (!sourceNode2.isField())
                    continue;

                identifyReflectionDependence(
                        sourceNode1.getType(), sourceNode2.getType(), sourceNode1, arg1SourceNodes, gadgetInfoRecord);
            }
        }
    }

    public static void identifyReflectionDependence(Type leftType, Type rightType,
                                                    SourceNode leftSourceNode,
                                                    HashSet<SourceNode> rightSourceNodes,
                                                    GadgetInfoRecord gadgetInfoRecord){
        DependenceNode dependenceNode = null;
        if ((leftType.toString().equals("java.lang.reflect.Method") & rightType.equals(leftType))
                || (ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("List"))
                    || ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("Map")))) {
            for (SourceNode rightSourceNode : rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_METHOD);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                } else if (rightSourceNode.getType().toString().equals("java.lang.String")) {
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.METHOD_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
        if (leftType.toString().equals("java.lang.Class") & rightType.equals(leftType)
                || (ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("List"))
                    || ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("Map")))) {
            for (SourceNode rightSourceNode : rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")) {
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_METHOD);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                } else if (rightSourceNode.getType().toString().equals("java.lang.String")) {
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
        if (leftType.toString().equals("java.lang.String") & rightType.equals(leftType)
                || (ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("List"))
                    || ClassRelationshipUtils.isSubClassOf(Utils.toSootClass(leftType), BasicDataContainer.commonClassMap.get("Map")))) {
            for (SourceNode rightSourceNode : rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")) {
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.METHOD_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                } else if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
        if (leftType.toString().equals("java.lang.Class")){
            for (SourceNode rightSourceNode: rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.String")) {
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
                else if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")){
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.CLASS_METHOD);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
        else if (leftType.toString().equals("java.lang.String")){
            for (SourceNode rightSourceNode: rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
                else if (rightSourceNode.getType().toString().equals("java.lang.reflect.Method")){
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_METHOD);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
        else if (leftType.toString().equals("java.lang.reflect.Method")){
            for (SourceNode rightSourceNode: rightSourceNodes) {
                if (rightSourceNode.getType().toString().equals("java.lang.Class")) {
                    dependenceNode = new DependenceNode(rightSourceNode, leftSourceNode, DependenceType.CLASS_METHOD);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
                else if (rightSourceNode.getType().toString().equals("java.lang.String")){
                    dependenceNode = new DependenceNode(leftSourceNode, rightSourceNode, DependenceType.METHOD_NAME);
                    gadgetInfoRecord.addDependenceNode(dependenceNode,true);
                }
            }
        }
    }
}
