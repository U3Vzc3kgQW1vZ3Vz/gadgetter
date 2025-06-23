package jdd.rules.sinks;

import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.config.RegularConfig;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.unit.RecordUtils;
import jdd.markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import jdd.util.ClassRelationshipUtils;
import jdd.util.DataSaveLoadUtil;
import callgraph.utilClass.StaticAnalyzeUtils.ClassUtils;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Used as detection rules for file writing class sink
 */
public class FileCheckRule extends AbstractCheckRule {

    public static HashSet<String> fileSinkSig = new HashSet<>();
    public static HashSet<String> fileClassNames = new HashSet<>();
// Backup

    public static boolean isValidType(Value value){
        String typeString = value.getType().toString();
        if (typeString.contains("byte[]") )
            return true;
        return false;
    }

    public FileCheckRule(){
        sinkType = SinkType.FILE;
    }

    public static void init() {
        fileClassNames = Utils.toStringSet(ClassUtils.getAllSubs(Utils.toSootClass("java.io.File")));
        fileClassNames.addAll(Utils.toStringSet(ClassUtils.getAllSubs(Utils.toSootClass("java.io.FileOutputStream"))));
        fileClassNames.addAll(Utils.toStringSet(ClassUtils.getAllSubs(Utils.toSootClass("java.io.OutputStream"))));
        fileSinkSig = Utils.toStringSet(ClassRelationshipUtils.getAllSubMethodSigs("<java.io.FileOutputStream: void write(byte[])>"));
        fileSinkSig.addAll(Utils.toStringSet(ClassRelationshipUtils.getAllSubMethodSigs("<java.io.OutputStream: void write(byte[])>")));
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
        InvokeExpr currentInvokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMethod = currentInvokeExpr.getMethod();
        String currentMtdSig = currentMethod.getSignature();
        ValueBox fileValueBox = Parameter.getThisValueBox(tfNode.node);

        if(fileSinkSig.contains(currentMtdSig) & fileValueBox != null){
            Value contentValue = currentInvokeExpr.getArg(0);
            risky = Utils.isTainted(contentValue, descriptor.taints)
                    && Utils.isTainted(fileValueBox.getValue(), descriptor.taints)
                    && (contentValue.getType().toString().contains("byte[]") || contentValue.getType().toString().contains("Byte[]") );

            HashSet<Value> taintedArgs = new HashSet<>();
            taintedArgs.add(contentValue);
            taintedArgs.add(fileValueBox.getValue());

            if (risky ){
                RecordUtils.recordTaintedArgs(descriptor, taintedArgs, sinkType, tfNode);
            }
        }
// }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        return fileSinkSig.contains(mtd.getSignature());
    }
}
