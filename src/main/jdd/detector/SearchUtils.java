package jdd.detector;

import callgraph.cfg.CFG;
import soot.SootClass;
import jdd.tranModel.Rules.TaintGenerateRule;
import jdd.container.BasicDataContainer;
import jdd.dataflow.InputTaintGenerator;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.collection.node.ClassNode;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.collection.node.GadgetNode;
import soot.SootMethod;

public class SearchUtils {
    public static InputTaintGenerator inputTaintGenerator = new InputTaintGenerator();

    public static MethodDescriptor initDealBeforeSearching(SootMethod sootMethod, SootClass thisClz){
        BasicDataContainer.resetState();

        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(sootMethod);
        inputTaintGenerator.generateTaints(descriptor, thisClz);
        descriptor.isEntry = true;
        descriptor.sourcesTaintGraph.entryMethod = sootMethod;

        if(descriptor.cfg == null){
            CFG cfg = new CFG(sootMethod, true);
            cfg.buildCFG();
            descriptor.cfg = cfg;
        }

        if (sootMethod.getName().equals("<init>"))
            TaintGenerateRule.fieldGenerate = false;
        else TaintGenerateRule.fieldGenerate = true;

        return descriptor;
    }

    public static MethodDescriptor initDealBeforeInferring(GadgetInfoRecord gadgetInfoRecord){
        SootMethod sourceGadget = gadgetInfoRecord.gadgets.getFirst();
        MethodDescriptor descriptor = initDealBeforeSearching(sourceGadget, null);

        GadgetNode gadgetNode = new GadgetNode(sourceGadget, gadgetInfoRecord.rootClass);
        if (gadgetInfoRecord.rootClassNode == null){
            ClassNode rootClassNode = new ClassNode(gadgetInfoRecord.rootClass, gadgetInfoRecord);
            gadgetInfoRecord.rootClassNode = rootClassNode;
            gadgetInfoRecord.classFieldsGraph.put(rootClassNode.sootClass, rootClassNode);
            rootClassNode.addGadgetNode(gadgetNode);
        }

        return descriptor;
    }


    public static void setDetectSchemeOn(){
        BasicDataContainer.gadgetParamsGenerate = true;
        BasicDataContainer.infosCollect = true;
        BasicDataContainer.openJoinRule = true;
    }

    public static void setDetectSchemeOff(){
        BasicDataContainer.gadgetParamsGenerate = false;
        BasicDataContainer.infosCollect = false;
        BasicDataContainer.openJoinRule = false;
    }
}
