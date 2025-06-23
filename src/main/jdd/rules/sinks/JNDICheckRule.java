package jdd.rules.sinks;

import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.config.RegularConfig;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.unit.RecordUtils;
import lombok.extern.slf4j.Slf4j;
import jdd.markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import jdd.util.ClassRelationshipUtils;
import jdd.util.DataSaveLoadUtil;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.io.IOException;
import java.util.*;

@Slf4j
public class JNDICheckRule extends AbstractCheckRule {
// Not only JNDI
    public static boolean isFineGrained = false;
// Signature used to record risk methods
    public static HashSet<String> riskyJNDIMethodsSig = new HashSet<>();
    public static HashSet<String> riskySPIMethodSig = new HashSet<>();
    public static HashSet<String> riskyConnectInputMethodSig = new HashSet<>();
    public static HashSet<String> riskyNDSMethodSig = new HashSet<>();
// The following are summarized expert experience, including the type of formal parameters of the method of the lookup that meets the requirements, known sink classes (basic, connection and SPILoad)
    public static List<String> riskyJNDIParamTypes = Arrays.asList("javax.naming.Name",
                                                                        "java.lang.String",
                                                                            "java.lang.Object",
                                                                                "javax.naming.Reference",
                                                                                    "java.util.Hashtable",
                                                                                        "javax.naming.Context");
    public static List<String> JNDIRiskyClassName = Arrays.asList("javax.naming.Context",
                                                                        "java.rmi.registry.Registry",
                                                                            "javax.naming.spi.ObjectFactory",
                                                                            "javax.naming.spi.NamingManager",
                                                                            "org.springframework.jndi.JndiTemplate");
    public static List<String> connectionRiskyClassName = Arrays.asList("java.net.URLConnection",
                                                                            "java.net.URL");
    public static List<String> SPILoadRiskyClassName = Arrays.asList("java.util.ServiceLoader");

    public static List<String> remoteLinkMethodsSig = new ArrayList<>();


    public JNDICheckRule(){
        sinkType = SinkType.JNDI;
    }

    public static void init() {
        riskyJNDIMethodsSig = ClassRelationshipUtils.getAllSubMethodSigs(JNDIRiskyClassName,"(lookup|getObjectInstance)");
        riskySPIMethodSig = ClassRelationshipUtils.getAllSubMethodSigs(SPILoadRiskyClassName,"(load)");
        riskyConnectInputMethodSig = ClassRelationshipUtils.getAllSubMethodSigs(connectionRiskyClassName,"(getInputStream|getContent|openStream)");
        riskyNDSMethodSig = ClassRelationshipUtils.getAllSubMethodSigs(Arrays.asList("java.net.InetAddress"),"(getByName)");
        remoteLinkMethodsSig.add("<sun.rmi.transport.LiveRef: sun.rmi.transport.Channel getChannel()>");
        remoteLinkMethodsSig.add("<sun.rmi.transport.LiveRef: void exportObject(sun.rmi.transport.Target)>");
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
        if (JNDICheck(descriptor,tfNode))
            risky = true;
        else if (SPICheck(descriptor,tfNode))
            risky = true;
        /*else if (connectionCheck(descriptor,transformableNode))
            risky = true;*/
// else if (DNSCheck(descriptor, tfNode))
// risky = true;
        else if (TCPPortCheck(descriptor, tfNode))
            risky = true;
        return risky;
    }

    private boolean TCPPortCheck(MethodDescriptor descriptor, TransformableNode tfNode){
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();

        if (remoteLinkMethodsSig.contains(currentMtdSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null){
                risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints);

                if (risky){
                    RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
                }
            }
        }

        return risky;
    }

    private boolean SPICheck(MethodDescriptor descriptor, TransformableNode tfNode) {
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();

        if (riskySPIMethodSig.contains(invokeExpr.getMethod().getSignature())){
            if (invokeExpr.getMethod().getParameterCount() == 2){
                Value arg = invokeExpr.getArg(1);
                risky = Utils.isTainted(arg, descriptor.taints);

                if (risky){
                    RecordUtils.recordTaintedArgs(descriptor, arg, sinkType, tfNode);
                }
            }
        }
        return risky;
    }

    private boolean JNDICheck(MethodDescriptor descriptor, TransformableNode tfNode) {
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();


// If it is the risky lookup method, and the first parameter is contaminated (the first parameter of the Lookup method is the class name/URL that the target is loaded)
        if (riskyJNDIMethodsSig.contains(currentMtdSig)){
            if (currentMtd.getParameterCount() > 0){
                for (Value arg: invokeExpr.getArgs()){
                    if (!riskyJNDIParamTypes.contains(arg.getType().toString()))
                        continue;
                    risky = Utils.isTainted(arg, descriptor.taints);

                    if (risky){
                        RecordUtils.recordTaintedArgs(descriptor, arg, sinkType, tfNode);
                        return risky;
                    }
                }
            }
        }
        return risky;
    }

    public boolean DNSCheck(MethodDescriptor descriptor, TransformableNode tfNode){
// java.net.InetAddress getByName
        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();

        if (riskyNDSMethodSig.contains(invokeExpr.getMethod().getSignature())){
            ValueBox argBox = Parameter.getArgByType(invokeExpr, "java.lang.String");
            if (argBox != null){
                risky = Utils.isTainted(argBox.getValue(), descriptor.taints);
                if (risky)
                    RecordUtils.recordTaintedArgs(descriptor, argBox.getValue(), sinkType, tfNode);
            }
        }

        return risky;
    }

    public boolean connectionCheck(MethodDescriptor descriptor,TransformableNode tfNode){

        boolean risky = false;
        InvokeExpr invokeExpr = tfNode.getUnitInvokeExpr();
        SootMethod currentMtd = invokeExpr.getMethod();
        String currentMtdSig = currentMtd.getSignature();

        if (riskyConnectInputMethodSig.contains(currentMtdSig)){
            ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
            if (thisValueBox != null){
                risky = Utils.isTainted(thisValueBox.getValue(), descriptor.taints);

                if (risky)
                    RecordUtils.recordTaintedArgs(descriptor, thisValueBox.getValue(), sinkType, tfNode);
            }
        }

        return risky;
    }

    @Override
    public boolean isSinkMethod(SootMethod mtd) {
        String methodSig = mtd.getSignature();
        return riskyJNDIMethodsSig.contains(methodSig)
                || riskySPIMethodSig.contains(methodSig)
                || riskyConnectInputMethodSig.contains(methodSig)
                || riskyNDSMethodSig.contains(methodSig)
                || remoteLinkMethodsSig.contains(methodSig);
    }

}
