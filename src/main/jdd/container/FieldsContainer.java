package jdd.container;

import jdd.PointToAnalyze.pointer.Pointer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.detector.SearchUtils;
import jdd.tranModel.TranUtil;
import jdd.tranModel.TransformableNode;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.Stmt;

import callgraph.utilClass.StaticAnalyzeUtils.ClassUtils;
import callgraph.utilClass.StaticAnalyzeUtils.FieldUtil;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;


public class FieldsContainer {
    public static HashMap<SootClass, HashMap<SootField, Value>> fieldStaticValueMap = new HashMap<>();

    public static HashMap<SootFieldRef, HashMap<SootMethod, HashSet<Value>>> fieldRefValuesMap = new HashMap<>();
    public static HashMap<SootClass, HashMap<SootField, Pointer>> fieldPointerInfosMap = new HashMap<>();

    public static void init(){
        constructFieldsPointerGraph();
    }

    /**
     * Capture the assignment information of fields during initialization
     */

    public static void constructFieldsPointerGraph(){
        HashSet<SootClass> allSootClz = new HashSet<>(Scene.v().getApplicationClasses());
        allSootClz.addAll(Scene.v().getClasses());
        for (SootClass sootClass: allSootClz){
            if (sootClass.resolvingLevel() < 3) continue;
// Analyze the information in the static code block, and the default assignment when initializing the object is not considered for the time being (because these fields are generally controllable by attackers)
            try {
                for (SootMethod sootMethod: sootClass.getMethods()){
                    if (sootMethod.getName().equals("<clinit>")
                            || sootMethod.getName().equals("<init>")){
                        recordFieldPoint(sootMethod, sootClass);
                    }
                }
            }catch (Exception e){}
        }
    }

    public static void recordFieldPoint(SootMethod sootMethod, SootClass sootClass){
        if (sootMethod == null)    return;
        MethodDescriptor clinitDescriptor = SearchUtils.initDealBeforeSearching(sootMethod, null);
        List<TransformableNode> topologicalOrder = TranUtil.getTopologicalOrderedTNodesFromCFG(clinitDescriptor.cfg);

        fieldStaticValueMap.put(sootClass, new HashMap<>());
        fieldPointerInfosMap.put(sootClass, new HashMap<>());

        for (TransformableNode tfNode: topologicalOrder){
            tfNode.forward(clinitDescriptor);
            if ((Stmt)tfNode.node.unit instanceof AssignStmt){
                AssignStmt assignStmt = (AssignStmt) tfNode.node.unit;
                Value left = assignStmt.getLeftOp();
                Value right = assignStmt.getRightOp();

                if (left instanceof FieldRef){
                    SootField sootField = ((FieldRef) left).getField();
                    if (right instanceof Constant){
                        fieldStaticValueMap.get(sootClass).put(sootField, right);
                    }else {
                        fieldStaticValueMap.get(sootClass).put(sootField, right);
                        Pointer pointer = clinitDescriptor.pointTable.getPointer(right);
                        if (pointer == null){
                            pointer = new Pointer(right.getType());
                        }
                        fieldPointerInfosMap.get(sootClass).put(sootField,pointer);
                    }
                }
            }
        }
    }


    public static SootField getSootFieldRefByStream(Value value, SootMethod sootMethod){
        for (SootFieldRef sootFieldRef: fieldRefValuesMap.keySet()){
            if (!fieldRefValuesMap.get(sootFieldRef).containsKey(sootMethod))
                continue;
            if (fieldRefValuesMap.get(sootFieldRef).get(sootMethod).contains(value))
                return FieldUtil.fromRefToSootField(sootFieldRef);
        }
        return null;
    }


    public static Value getStaticSootFieldInfo(SootField sootField, SootClass sootClass){
        SootClass curClass = sootClass;
        if (sootClass == null){
            curClass = sootField.getDeclaringClass();
        }
        if (fieldStaticValueMap.containsKey(curClass))
            if (fieldStaticValueMap.get(curClass).containsKey(sootField))
                return fieldStaticValueMap.get(curClass).get(sootField);

        for (SootClass superClass: ClassUtils.getAllSupers(curClass)){
            if (!fieldStaticValueMap.containsKey(superClass))  continue;
            if (fieldStaticValueMap.get(superClass).containsKey(sootField))
                return fieldStaticValueMap.get(superClass).get(sootField);
        }

        return null;
    }


    public static Pointer getFieldPointer(SootField sootField, SootClass sootClass){
        SootClass curClass = sootClass;
        if (sootClass == null){
            curClass = sootField.getDeclaringClass();
        }

        if (fieldPointerInfosMap.containsKey(curClass))
            if (fieldPointerInfosMap.get(curClass).containsKey(sootField))
                return fieldPointerInfosMap.get(curClass).get(sootField);

        for (SootClass superClass: ClassUtils.getAllSupers(curClass)){
            if (!fieldPointerInfosMap.containsKey(superClass))  continue;
            if (fieldPointerInfosMap.get(superClass).containsKey(sootField))
                return fieldPointerInfosMap.get(superClass).get(sootField);
        }

        return null;
    }
}
