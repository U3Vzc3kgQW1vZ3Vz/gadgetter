package jdd.rules.sinks;

import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.config.RegularConfig;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.unit.RecordUtils;
import jdd.markers.SinkType;
import soot.SootField;
import soot.SootMethod;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import jdd.util.ClassRelationshipUtils;
import jdd.util.DataSaveLoadUtil;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;

public class SecondDesCheckRule extends AbstractCheckRule {
    public static HashSet<String> unsafeDesProtocols = new HashSet<>();

    public static void init(){
        unsafeDesProtocols = ClassRelationshipUtils.getAllSubMethodSigs("<java.io.ObjectInputStream: java.lang.Object readObject()>");
    }

    public SecondDesCheckRule(){
        sinkType = SinkType.SECOND_DES;
    }

    @Override
    public void apply(MethodDescriptor descriptor, LinkedList<SootMethod> callStack, Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        if (!tfNode.containsInvoke())   return;

        SootMethod currentInvokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        if (checkRisky(descriptor,tfNode)){
            callStack.add(currentInvokedMethod);
            if (!super.checkGadgetDuplication(callStack, sinkType)){
                FragmentsContainer.updateSinkFragment(callStack,sinkType, tfNode, descriptor);
// DataSaveLoadUtil.recordCallStackToFile(callStack, sinkType,
// RegularConfig.outputDir + "/gadgets/interInfos/" + sinkType.toString() + "SinkFragments.txt",
// true);
                DataSaveLoadUtil.recordCallStackToFile(callStack, sinkType,
                        RegularConfig.outputDir + "/gadgets/interInfos/" +"GadgetChains.txt",
                        true);
            }
            callStack.remove(currentInvokedMethod);
        }
    }

    @Override
    public boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();

        if (unsafeDesProtocols.contains(currentMtdSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null) {
                SootField field = descriptor.getField(tfNode.node, Parameter.getThisValueBox(tfNode.node));
                risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints) & field != null
                        & thisValueBox.getValue().getType().toString().equals("byte[]");

                if (risky ){
                    RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
                }
            }
        }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        return unsafeDesProtocols.contains(mtd.getSignature());
    }

}
