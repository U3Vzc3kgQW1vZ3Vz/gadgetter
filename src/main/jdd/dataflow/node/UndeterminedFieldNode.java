package jdd.dataflow.node;

import jdd.tranModel.Taint.Taint;
import jdd.util.Pair;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Value;

import java.util.HashMap;
import java.util.LinkedHashMap;


public class UndeterminedFieldNode {
    LinkedHashMap<Value, Pair<SootMethod, SootClass>> undeterminedLocalValues = new LinkedHashMap<>();
    HashMap<Value, Pair<SootMethod, Value>> interValueRela = new HashMap<>();


    public void updateSourceOfFields(Taint taint,
                                     MethodDescriptor descriptor,
                                     SootFieldRef sootFieldRef){
        for (Taint ailasTaint: taint.aliases){
// Only accessPath.isEmpty() is recorded, because the pollution between fields is not considered when building the field graph, and the alias field may belong to the impact between fields
            if (!ailasTaint.accessPath.isEmpty())
                continue;

            for (Value value: undeterminedLocalValues.keySet()){
                if (!value.equals(ailasTaint.object))
                    continue;
                Pair<SootMethod, SootClass> pair = undeterminedLocalValues.get(value);
                if (!descriptor.sootMethod.equals(pair.getKey()))
                    continue;
                if (!descriptor.getCurrentClass().equals(pair.getValue()))
                    continue;


            }
        }
    }
}
