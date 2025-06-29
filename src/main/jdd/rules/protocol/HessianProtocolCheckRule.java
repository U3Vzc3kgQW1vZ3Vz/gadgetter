package jdd.rules.protocol;

import jdd.config.RegularConfig;
import lombok.extern.slf4j.Slf4j;
import jdd.rules.sinks.*;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import jdd.util.ClassRelationshipUtils;
import jdd.util.Utils;

import java.util.Arrays;
import java.util.HashSet;

import static jdd.util.ClassRelationshipUtils.getMethodOfClassAndSuper;

@Slf4j
public class HessianProtocolCheckRule extends AbstractProtocolCheckRule{

    @Override
    public void init() {
// Not adding toString for the time being. Although some protocols can be set toString as an entry method; the application scope from Map.put is wider
        entryMethods = new HashSet<>(Arrays.asList("java.lang.Object put(java.lang.Object,java.lang.Object)"));
        this.setSinkCheckRule();
        updateEntryMethods();
    }

    public boolean needEqualsTrigger() {
        return !RegularConfig.derivationType.equals("SecondDesDerivation")
            & !RegularConfig.derivationType.equals("InvokeDerivation");
    }

    @Override
    public HashSet<SootMethod> getSourceMethods() {
        doClassCheck();

        HashSet<SootMethod> sourceMethods = ClassRelationshipUtils.getAllSubMethods(
                Utils.toSootMethod("<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>")
        );

        HashSet<SootMethod> toDelete = new HashSet<>();
        for (SootMethod sootMethod: sourceMethods){
            if (!candidateClassSet.contains(sootMethod.getDeclaringClass()))
                toDelete.add(sootMethod);
        }

        sourceMethods.removeAll(toDelete);

        SootMethod equalMtd = Scene.v().getMethod("<java.lang.Object: boolean equals(java.lang.Object)>");
        for (SootClass sootClass: candidateClassSet){
            SootMethod equalsMtd = getMethodOfClassAndSuper(sootClass, equalMtd.getSubSignature());
            if (equalsMtd != null)
                this.fsMtds.add(equalsMtd);
        }

        this.sources = sourceMethods;

        return sourceMethods;
    }


    void setSinkCheckRule(){
        if (RegularConfig.sinkRules.contains("classLoad")) {
            ClassLoaderCheckRule classLoaderCheckRule = new ClassLoaderCheckRule();
            sinkCheckRule.put(classLoaderCheckRule.sinkType, classLoaderCheckRule);
        }
        if (RegularConfig.sinkRules.contains("invoke")) {
            InvokeCheckRule invokeCheckRule = new InvokeCheckRule();
            sinkCheckRule.put(invokeCheckRule.sinkType, invokeCheckRule);
        }
        if (RegularConfig.sinkRules.contains("jndi")) {
            JNDICheckRule JNDICheckRule = new JNDICheckRule();
            sinkCheckRule.put(JNDICheckRule.sinkType, JNDICheckRule);
        }
        if (RegularConfig.sinkRules.contains("secondDes")) {
            SecondDesCheckRule secondDesCheckRule = new SecondDesCheckRule();
            sinkCheckRule.put(secondDesCheckRule.sinkType, secondDesCheckRule);
        }
        if (RegularConfig.sinkRules.contains("exec")) {
            ExecCheckRule execCheckRule = new ExecCheckRule();
            sinkCheckRule.put(execCheckRule.sinkType, execCheckRule);
        }
        if (RegularConfig.sinkRules.contains("custom")){
            CustomCheckRule customCheckRule = new CustomCheckRule();
            sinkCheckRule.put(customCheckRule.sinkType,  customCheckRule);
        }
    }
}
