package jdd.dataflow.node;

import java.DefaultDetector.DefaultMethodDescriptor;
import jdd.PointToAnalyze.pointer.PointTable;
import jdd.PointToAnalyze.pointer.Pointer;
import jdd.tranModel.Taint.Taint;
import jdd.tranModel.TransformableNode;
import java.cfg.CFG;
import java.cfg.Node;
import jdd.dataflow.node.paramResult.MethodResult;
import jdd.dataflow.node.paramResult.TaintAndLinger;
import lombok.extern.slf4j.Slf4j;
import jdd.markers.SinkType;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.ReturnStmt;
import jdd.util.ClassRelationshipUtils;
import jdd.util.Utils;

import java.util.*;

import static java.dataflow.DataFlow.findAllDefUnitAffectThisValue;

@Slf4j
public class MethodDescriptor extends DefaultMethodDescriptor {
    public CFG cfg = null;

    public SootClass currentClass = null;
    public boolean isDynamicEntry = false;
    public boolean isEntry = false;
    public boolean isDynProxyEntry = false;

// Local context sensitivity
    public boolean visited  = false;
    public HashMap<TaintAndLinger, MethodResult> memorize = new HashMap<>();
    public SootField equalsField = null;


    public PointTable pointTable = new PointTable(this);
    public HashMap<Integer, Pointer> paramValInfo = new HashMap<>();

    public HashMap<Integer, Value> paramIdMapLocalValue = new HashMap<>();

    public HashMap<Integer, List<Taint>> paramBeTainted = new HashMap<>();
    public HashMap<Integer, List<Taint>> inputParamMapTaints = new HashMap<>();

    public HashSet<Taint> taints = new HashSet<>();
    public HashSet<Taint> newtaints = new HashSet<>();
// Maintain all the created taits, some of which may not be actually contaminated (alias analysis), and the actual contaminated is in the tait
    public HashSet<Taint> allTaints = new HashSet<>();
// Record the polluted object in the return value
    public HashSet<Taint> retTainted = new HashSet<>();
    public ReturnStmt returnStmt = null;

    public HashMap<Integer, HashSet<SourceNode>> fieldsParamIndexRecord = new HashMap<>();
    public SourcesTaintGraph sourcesTaintGraph = new SourcesTaintGraph();

    public HashMap<SinkType, HashMap<TransformableNode, HashSet<SourceNode>>> sinkUnitsRecord = new HashMap<>();

    public HashSet<Value> tempGeneratedObjs = new HashSet<>();


    public MethodDescriptor(SootMethod method) {
        super(method);
        sourcesTaintGraph.descriptor = this;
    }


    public boolean needDetect(){
        if (!visited)
            return true;

        int paramTaint = 0;
for (Integer ind: inputParamMapTaints.keySet()){ // Dirty record
            if (!inputParamMapTaints.get(ind).isEmpty()){
                paramTaint |= (1 << (ind + 1));
            }
        }

        for (Integer ind = inputParamMapTaints.size(); ind < inputParamMapTaints.size() + fieldsParamIndexRecord.size(); ind++){
            if (fieldsParamIndexRecord.containsKey(ind - inputParamMapTaints.size()))
                if (!fieldsParamIndexRecord.get(ind - inputParamMapTaints.size()).isEmpty())
                    paramTaint |= (1 <<(ind+1));
        }
        TaintAndLinger tmp = new TaintAndLinger(paramTaint);

        if (memorize.containsKey(tmp)){
            paramBeTainted = memorize.get(tmp).paramBeTainted;
            retTainted = memorize.get(tmp).retTainted;
           return false;
        }

        return true;
    }

    public void flushStates(){
        currentClass = null;

        allTaints = new HashSet<>();
        taints = new HashSet<>();
        newtaints = new HashSet<>();

        paramIdMapLocalValue = new HashMap<>();
        paramBeTainted = new HashMap<>();
        retTainted = new HashSet<>();
        pointTable = new PointTable(this);
        sourcesTaintGraph.sources2TaintedValues = new HashMap<>();
        sourcesTaintGraph.sourceUnFound = new HashMap<>();
    }

    /**
     * Return an existing stain or create a new stain:
     * 1. If object is null, then return directly to new Taint(null, accessPath);
     * 2. If object is not null:
     * a. AccessPath is null, then check whether there is an existing stain. If there is one, return it if it does not. If it does not, it will be created and returned.
     * b. accessPath is not null, same as above
     * accessPath is used to record a polluted field in a class
     * @param object
     * @param accessPath
     * @return
     */
    public Taint getOrCreateTaint(Value object, LinkedList<SootField> accessPath){

        if(object == null){
            return new Taint(null, accessPath);
        }

        if(accessPath == null){
            for(Taint taint : allTaints){
                if(taint.object.equals(object)){
                    if(taint.accessPath.isEmpty()){
                        return taint;
                    }
                }
            }
            Taint taint = new Taint(object);
            Taint.addTaint(taint, allTaints);
            return taint;
        } else{
            for(Taint taint : allTaints){
                if(taint.object.equals(object)){
                    if(Utils.listEqual(accessPath, taint.accessPath)){
                        return taint;
                    }
                }
            }
            Taint taint = new Taint(object, accessPath);
            Taint.addTaint(taint, allTaints);
            return taint;
        }

    }


    public List<Taint> getAllTaintsAboutThisValue(Value object){
        List<Taint> taintsForValue = new LinkedList<>();
        for(Taint taint : this.taints){
            if(taint.object.equals(object)){
                taintsForValue.add(taint);
            }
        }
        return taintsForValue;
    }

    /**
     * Get all new taints about this value, excluding the initial incoming taints
     * Like getAllTaintsAboutThisValue, both fields-sensitive matches are not considered
     */
    public List<Taint> getAllNewTaintsAboutThisValue(Value object){
        List<Taint> taintsForValue = new LinkedList<>();
        for(Taint taint : this.newtaints){
            if(taint.object.equals(object)){
                taintsForValue.add(taint);
            }
        }
        return taintsForValue;
    }

    /**
     * 1. Given mayTaint to determine whether there is a current stain list. If it returns ture, it returns false
     * 2. Given a beAddBox related to mayTaint, such as a = b.Fuc(c); If c is a stain, then obviously the stain needs to be passed to a
     * @param mayTaint
     * @param beAddBox
     * @return
     */
    public boolean addTaint(Value mayTaint, ValueBox beAddBox){
        boolean risky = false;
        for (Taint taint: taints){
            if (taint.object.equals(mayTaint)){
                risky = true;

                if (beAddBox != null){
                    Taint newTaint = getOrCreateTaint(beAddBox.getValue(), new LinkedList<>(taint.accessPath));
                    Taint.addTaint(newTaint,taints);
                }
                break;
            }
        }

        return risky;
    }

    /**
     * Check the stains and make necessary updates
     * (1) Check whether the stain is legal: whether it is null
     */
    public void flushTaints(){
        HashSet<Taint> toDelete = new HashSet<>();
        for (Taint taint: taints){
            if (taint == null)
                toDelete.add(taint);
        }
        taints.removeAll(toDelete);

        toDelete = new HashSet<>();
        for (Taint taint: allTaints){
            if (taint == null)
                toDelete.add(taint);
        }
        allTaints.removeAll(toDelete);

        toDelete = new HashSet<>();
        for (Taint taint: newtaints){
            if (taint == null)
                toDelete.add(taint);
        }
        newtaints.removeAll(toDelete);
    }

    public SootField getField(Node sourceNode, ValueBox valueBox) {
        if (valueBox == null) return null;
        SourceNode sourceNodeOfField = getFieldSourceNode(sourceNode, valueBox);
        if (sourceNodeOfField != null)
            return sourceNodeOfField.field.getFirst();

        return getFieldDirectly(sourceNode, valueBox);
    }

    public SourceNode getFieldSourceNode(Node sourceNode, ValueBox valueBox){
        HashSet<SourceNode> sources = sourcesTaintGraph.matchTaintedSources(valueBox.getValue());
        for (SourceNode source : sources){
            if (source.isField()){
SootField sootField = source.field.getLast(); // The last one is returned by default, which is the innermost field
                if (valueBox.getValue().getType().toString().equals("java.lang.Object")
                        | (valueBox.getValue().getType().equals(sootField.getType()))
                        | ClassRelationshipUtils.isSubClassOf(
                        Utils.toSootClass(valueBox.getValue().getType()), Utils.toSootClass(sootField.getType()))
                        | (sootField.getType().toString().contains(valueBox.getValue().getType().toString()))){
                    return source;
                }
            }
        }
        return null;
    }

    public SootField getFieldDirectly(Node sourceNode, ValueBox valueBox) {
        if (valueBox == null) return null;
        if (valueBox.getValue() instanceof FieldRef)
            return ((FieldRef) valueBox.getValue()).getField();

        LinkedHashSet<Node> sources = findAllDefUnitAffectThisValue(sourceNode,valueBox);

        Value taint = valueBox.getValue();
        for (Node node: sources){
            if (node.unit instanceof AssignStmt){
                Value left = ((AssignStmt)node.unit).getLeftOp();
                Value right = ((AssignStmt)node.unit).getRightOp();

                if (left.equals(taint)){
                    if (right instanceof FieldRef)
                        return ((FieldRef) right).getField();
                    taint = right;
                }
            }
        }
        return null;
    }

    public SootClass getCurrentClass() {
        if (currentClass != null)
            return currentClass;
        if (paramValInfo.containsKey(-1)){
            Pointer thisPointer = paramValInfo.get(-1);
            SootClass tmpClassOfPointerType = Utils.toSootClass(thisPointer.getType());
            if (ClassRelationshipUtils.isSubClassOf(tmpClassOfPointerType, sootMethod.getDeclaringClass()))
                currentClass = Utils.toSootClass(thisPointer.getType());
            else currentClass = sootMethod.getDeclaringClass();
        }else {
            currentClass = sootMethod.getDeclaringClass();
        }
        return currentClass;
    }
}
