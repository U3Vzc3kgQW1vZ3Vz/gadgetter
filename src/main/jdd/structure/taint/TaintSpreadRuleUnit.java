package jdd.structure.taint;
sub method signature matching;
Only match method names
import soot.SootField;
import jdd.util.Pair;
import soot.Scene;
import soot.SootMethod;
import jdd.util.ClassRelationshipUtils;
import java.util.StaticAnalyzeUtils.MethodUtil;
import jdd.util.Utils;

import java.util.HashMap;
import java.util.HashSet;

public class TaintSpreadRuleUnit {
    public HashMap<Integer, HashSet<Integer>> taintsConditionRecord = new HashMap<>();
    public HashMap<Integer, HashSet<Integer>> paramsBeTainted = new HashMap<>();

    public HashMap<Integer, HashSet<Pair<Integer,Integer>>> taintInfluenceRecord = new HashMap<>();
    public Integer indexMax = -2;
// Record the relevant method signature
    public String methodSig;
    public boolean extendFlag = true;
    public HashSet<String> methodSigs = new HashSet<>();

    public boolean needInfluenceCheck = false;
public int checkLevel = 3; // 3 (strictest): method signature;
    public boolean serializableCheckFlag = true;
    public HashMap<Integer, HashSet<String>> taintInfluenceFieldsRecord = new HashMap<>();

    public void init(){
        SootMethod sootMethod = null;
        if (extendFlag ) {
            if (checkLevel == 3) {
                sootMethod = Utils.toSootMethod(methodSig);
                if (sootMethod == null)
                    return;
                HashSet<SootMethod> sootMethods = ClassRelationshipUtils.getAllSubMethods(sootMethod);
                methodSigs = Utils.toMethodSigs(sootMethods);
            }
            else if (checkLevel == 2){
                for (SootMethod tmpSootMethod: Scene.v().getMethodNumberer()){
                    if (tmpSootMethod.getSubSignature().equals(methodSig))
                        methodSigs.add(tmpSootMethod.getSignature());
                }
            }
        }else methodSigs.add(methodSig);
        for (Integer hashCode: taintsConditionRecord.keySet()){
            for (int ind: taintsConditionRecord.get(hashCode)) {
                if (ind > indexMax)
                    indexMax = ind;
            }
            for (int ind: paramsBeTainted.get(hashCode)) {
                if (ind > indexMax)
                    indexMax = ind;
            }
            for (Pair<Integer,Integer> pair: taintInfluenceRecord.get(hashCode)){
                if (pair.getKey() > indexMax)
                    indexMax = pair.getKey();
                if (pair.getValue() > indexMax)
                    indexMax = pair.getValue();

            }
        }
        for (HashSet<Integer> inds: taintsConditionRecord.values()){
            for (int ind: inds) {
                if (ind > indexMax)
                    indexMax = ind;
            }
        }

        if (checkLevel == 3 & sootMethod != null) {
            if (sootMethod.getParameterCount() <= indexMax)
                System.out.println("???");
            assert sootMethod.getParameterCount() > indexMax;
        }
    }
}
