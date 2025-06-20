package jdd.rules.protocol;

import jdd.config.RegularConfig;
import lombok.extern.slf4j.Slf4j;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import jdd.util.ClassRelationshipUtils;

import java.util.Arrays;
import java.util.HashSet;

import static jdd.util.ClassRelationshipUtils.getMethodOfClassAndSuper;

@Slf4j
public class JdkNativeProtocolCheckRule extends AbstractProtocolCheckRule {


    @Override
    public void init() {
        entryMethods = new HashSet<>(Arrays.asList("void readObjectNoData()", "void readObject(java.io.ObjectInputStream)",
                "void readExternal(java.io.ObjectInput)", "java.lang.Object readResolve()"));
        this.setSinkCheckRule();
        updateEntryMethods();
    }

    public boolean needEqualsTrigger() {
        return !RegularConfig.derivationType.equals("SecondDesDerivation")
                && !RegularConfig.derivationType.equals("InvokeDerivation");
    }

    @Override
    public HashSet<SootMethod> getSourceMethods() {
doClassCheck(); // Filter class

        HashSet<SootMethod> sourceMethods = new HashSet<>();
        SootMethod equalMtd = Scene.v().getMethod("<java.lang.Object: boolean equals(java.lang.Object)>");
// Extract source methods according to the logic of this protocol
        for (SootClass sootClass: candidateClassSet){
            sourceMethods.addAll(ClassRelationshipUtils.getMethods(sootClass,entryMethods));

            SootMethod equalsMtd = getMethodOfClassAndSuper(sootClass, equalMtd.getSubSignature());
            if (equalsMtd != null)
                this.fsMtds.add(equalsMtd);
        }

        this.sources = sourceMethods;
        return sourceMethods;
    }


}
