package jdd.detector;

import jdd.PointToAnalyze.pointer.Pointer;
import jdd.config.ConfigUtil;
import jdd.config.InitConfig;
import jdd.config.RegularConfig;
import jdd.config.SootConfig;
import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import jdd.dataflow.DataFlowAnalysisUtils;
import jdd.dataflow.DataflowDetect;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import jdd.dataflow.node.UndeterminedFieldNode;
import fj.P;
import jdd.gadgets.collection.iocd.unit.instrument.Instruments;
import jdd.gadgets.collection.node.ClassNode;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.unit.Fragment;
import lombok.extern.slf4j.Slf4j;
import jdd.markers.SinkType;
import jdd.markers.Stage;
import soot.*;
import soot.jimple.AddExpr;
import soot.jimple.Expr;
import soot.jimple.XorExpr;
import jdd.tranModel.Rule;
import jdd.tranModel.Rules.RuleUtils;
import jdd.tranModel.TranUtil;
import jdd.tranModel.TransformableNode;
import jdd.util.DataSaveLoadUtil;
import jdd.util.Pair;
import java.util.StaticAnalyzeUtils.Parameter;
import java.util.TimeOutTask;
import jdd.util.Utils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import static jdd.dataflow.DataFlowAnalysisUtils.flushSinkFragmentsBasedOnPriority;
import static jdd.detector.SearchUtils.*;
import static jdd.gadgets.collection.iocd.TransformerUtils.*;
import static jdd.util.ClassRelationshipUtils.isProxyMethod;

@Slf4j
public class SearchGadgetChains {
    public static int timeThread = 30;
    public static DataflowDetect dataflowDetect = new DataflowDetect();

    public static void detect() throws Exception {
// 1. Initialization
        InitConfig.initAllConfig();

// 2. Search for Gadget Fragment
        log.info("[ Fragments Searching]");
        searchGadgetFragments();

// 3. Gadget Fragment splicing
        log.info("[ Fragments Linking]");
        linkFragments();

// Generate IOCD information
        if (RegularConfig.outPutIOCD) {
            System.out.println("[ IOCD Generating ]");
            buildIOCD();
        }else {
            System.out.println("[ Print Detected Gadget Chains ]");
// just print the detected chains, see the detected chains in DetectedGadgetChains.txt
            String targetResultsPath = RegularConfig.outputDir + File.separator + "gadgets" + File.separator + RegularConfig.outPutDirName + File.separator;
            DataSaveLoadUtil.createDir(targetResultsPath);
            for (HashSet<Fragment> sinkFragments : FragmentsContainer.sortedSinkFragmentsMap.values()) {
                for (Fragment sinkFragment : sinkFragments) {
                    DataSaveLoadUtil.recordCallStackToFile(sinkFragment.gadgets, sinkFragment.sinkType,
                            targetResultsPath+ "DetectedGadgetChains.txt",
                            true);
                }
            }
        }
    }

    public static void searchGadgetFragments() {
setDetectSchemeOn(); // Set the flag to start detection
        while (!FragmentsContainer.sources.isEmpty()) {
            SootMethod headMtd = FragmentsContainer.sources.iterator().next();
            FragmentsContainer.sources.remove(headMtd);
            FragmentsContainer.searched.add(headMtd);
            searchFragment(headMtd, null);

if (FragmentsContainer.superMtdSources.containsKey(headMtd)) { // 考虑
                while (!FragmentsContainer.superMtdSources.get(headMtd).isEmpty()) {
                    SootClass thisClz = FragmentsContainer.superMtdSources.get(headMtd).iterator().next();
                    FragmentsContainer.superMtdSources.get(headMtd).remove(thisClz);
                    FragmentsContainer.searched.add(headMtd);
                    searchFragment(headMtd, thisClz);
                }
            }
        }
        setDetectSchemeOff();
    }

    public static boolean collectFields(SootMethod sootMethod, HashSet<SourceNode> usedFields) {
// Generate stain information for the initial method
        MethodDescriptor descriptor = initDealBeforeSearching(sootMethod, null);
        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(sootMethod);

// Expand the data flow
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("Search for related fields in the method" + sootMethod.getSignature());
                    dataflowDetect.collectFields(sootMethod, usedFields, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("Timeout when analyzing method" + sootMethod.getName() + ". Located in class"
                            + sootMethod.getDeclaringClass());
                }
            }.run(180);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return false;
        }

        return !callStack.contains(null);
    }


    public static boolean isValidFixedHashCode(boolean flag, SootMethod sootMethod,
                                               HashSet<SourceNode> usedFields,
                                               LinkedList<SootMethod> callStack) throws IOException {
        MethodDescriptor descriptor = DataFlowAnalysisUtils.getMethodDescriptor(sootMethod);
        if (descriptor == null) return flag;

// Update the information of calling the method to the method; inter-process analysis
        HashSet<Value> hashCodeValues = new HashSet<>();

        DataFlowAnalysisUtils.updateInterInfos(descriptor);
        List<TransformableNode> topologicalOrder = TranUtil.getTopologicalOrderedTNodesFromCFG(descriptor.cfg);
        for (TransformableNode tfNode : topologicalOrder) {
            HashMap<SourceNode, HashSet<Pair<String, Integer>>> ret = DataFlowAnalysisUtils.extractUsedFields(tfNode, descriptor);
// Record the fields used
            for (SourceNode sourceNode : ret.keySet()) {
                if (sourceNode.classOfField.equals(descriptor.getCurrentClass()))
                    usedFields.add(sourceNode);
            }
        }

        for (TransformableNode tfNode : topologicalOrder) {
// The hashCode() method is called, and the local values corresponding to the fields of hashCode are calculated.
            if (tfNode.containsInvoke()) {
                SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();

                if (invokedMethod.getSubSignature().equals("int hashCode()")) {
                    ValueBox valueBox = Parameter.getThisValueBox(tfNode.node);
                    if (valueBox != null) {
                        Pointer thisPointer = descriptor.pointTable.getPointer(valueBox.getValue());
                        if (thisPointer != null && thisPointer.getType().toString().equals("java.lang.Class")) continue;
                    }
                    Value retValue = Parameter.getReturnedValue(tfNode.node);
                    hashCodeValues.add(retValue);
                }
            }

            for (ValueBox valueBox : tfNode.node.unit.getUseAndDefBoxes()) {
                if (valueBox == null)
                    continue;
                if (!hashCodeValues.contains(valueBox.getValue()))
                    continue;

                if (valueBox.getValue() instanceof Expr) {
                    if (!(valueBox.getValue() instanceof XorExpr
                            | valueBox.getValue() instanceof AddExpr)) {
                        flag = false;
                    }
                }
            }

            DataFlowAnalysisUtils.checkTransformable(tfNode, descriptor, callStack);

            if (tfNode.containsInvoke() & callStack.size() <= BasicDataContainer.stackLenLimitForFieldsCollection) {
                if (DataFlowAnalysisUtils.continueCheck(tfNode, descriptor)) {
                    HashMap<Integer, Pointer> inputCallFrame = DataFlowAnalysisUtils.getMethodBaseParamInfo(tfNode, descriptor);
                    HashSet<SootMethod> invokedMethods = DataFlowAnalysisUtils.getInvokedMethods(tfNode, descriptor);
                    if (invokedMethods.size() > 10) {
                        callStack.add(null);
                        return flag;
                    }

                    for (SootMethod invokedMethod : invokedMethods) {
                        MethodDescriptor invokedDescriptor = DataFlowAnalysisUtils.flowInvokedMethod(descriptor, invokedMethod, inputCallFrame, callStack, tfNode);
                        if (invokedDescriptor == null | sootMethod.equals(invokedMethod)) {
                            callStack.add(null);
                            return flag;
                        }
                        flag = isValidFixedHashCode(flag, invokedMethod, usedFields, callStack);
                        DataFlowAnalysisUtils.outInvokedMethod(invokedDescriptor, descriptor, tfNode, callStack);
                    }
                } else {
                    callStack.add(null);
                }
            }
        }

        DataFlowAnalysisUtils.updateAfterAnalysisMtd(descriptor);
        return flag;
    }


    /**
     * 构建以sootMethod作为entry的 fields-taints Graph
     *
     * @param sootMethod
     */
    public static void constructFieldsTaintGraph(SootMethod sootMethod) {
        BasicDataContainer.stage = Stage.TAINT_FIELDS_GRAPH_BUILD;
        MethodDescriptor descriptor = initDealBeforeSearching(sootMethod, null);
        LinkedList<SootMethod> callStack = new LinkedList<>();
        HashSet<UndeterminedFieldNode> undeterminedFieldNodes = new HashSet<>();
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("Search for related fields in the method: " + sootMethod.getSignature());
                    dataflowDetect.constructFieldsTaintGraph(sootMethod, callStack, undeterminedFieldNodes);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("Timeout when analyzing method" + sootMethod.getName() + ". Located in class"
                            + sootMethod.getDeclaringClass());
                }
            }.run(180);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }
    }


    /**
     * 对 startMtd 作为起始方法, 搜索并记录 Fragment 信息
     * (1) 搜索过程中检测到的其他动态方法
     * (2) 入参与动态方法调用参数之间的映射关系
     * (3) 生成的Fragment的相关信息: Fragment类型,
     *
     * @param headMtd
     */
    public static void searchFragment(SootMethod headMtd, SootClass thisClass) {
        if (FragmentsContainer.isSinkMethod(headMtd) || RuleUtils.isInvalidFragmentEnd(headMtd, false))
            return;
        BasicDataContainer.stage = Stage.FRAGMENT_SEARCHING;

        MethodDescriptor descriptor = initDealBeforeSearching(headMtd, thisClass);

        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(headMtd);

// Expand the data flow
        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    log.info("[Identifying Fragment] searching from: " + headMtd.getSignature());
                    dataflowDetect.detectFragment(descriptor, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("Timeout when analyzing method" + headMtd.getName() + ". Located in class"
                            + (thisClass==null? headMtd.getDeclaringClass(): thisClass));
                }
            }.run(timeThread);
        } catch (Exception e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }

        descriptor.isEntry = false;
    }

    /**
     * 进行 Fragments 的拼接
     * TODO 未迁移的功能: 拼接后更细粒度的污点检查 & 无用fragments的
     */
    public static void linkFragments() {
        if (!FragmentsContainer.protocolCheckRule.openBPLink()) {
            FragmentsContainer.gadgetFragments = FragmentsContainer.sinkFragments;
            FragmentsContainer.sortSinkFragments();
            return;
        }


        BasicDataContainer.stage = Stage.FRAGMENT_LINKING;

        LinkedHashSet<Fragment> newSinkFragments = new LinkedHashSet<>();
        HashSet<Fragment> freeStateFragments = new HashSet<>(
                FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.FREE_STATE)
        );
        LinkedHashSet<Fragment> allSinkFragments = new LinkedHashSet<>(FragmentsContainer.sinkFragments);
        HashSet<SootMethod> dynamicMethods = new HashSet<>();
        HashSet<SootMethod> dynamicMethodsNext = new HashSet<>();
        for (Fragment sinkFragment : allSinkFragments) {
            dynamicMethods.addAll(sinkFragment.connectRequire.preLinkableMethods);
        }
        int linkCount = 0;

// Iteration
        while (!dynamicMethods.isEmpty() && linkCount <= BasicDataContainer.linkTimeLimit) {
            newSinkFragments.clear();
            HashSet<Fragment> toDelete = new HashSet<>();
            for (Fragment freeStateFragment : freeStateFragments) {
                if (!dynamicMethods.contains(freeStateFragment.end))
                    continue;

                HashSet<Fragment> addSinkFragments = dataflowDetect.linkFreeStateFragments(freeStateFragment);
                if (!addSinkFragments.isEmpty()) toDelete.add(freeStateFragment);
for (Fragment newSinkFragment : addSinkFragments) { // TODO: Add switch to select whether to enable heuristic selection
                    flushSinkFragmentsBasedOnPriority(newSinkFragment, allSinkFragments, newSinkFragments);

                    HashSet<SootMethod> newDynamicMtds = new HashSet<>(newSinkFragment.connectRequire.preLinkableMethods);
                    newDynamicMtds.removeAll(dynamicMethods);
                    if (!newDynamicMtds.isEmpty()) {
                        dynamicMethodsNext.addAll(newDynamicMtds);
                        dynamicMethods.addAll(newDynamicMtds);
                    }
                }
            }
// After obtaining all new Sink Fragments, update the global sinkFragments to the new ones added in this round.
// and delete these Fragments from Free-State Fragments
            FragmentsContainer.sinkFragments = new HashSet<>(newSinkFragments);
            if (newSinkFragments.isEmpty() || dynamicMethodsNext.isEmpty()) {
                break;
            }
            dynamicMethods = new HashSet<>(dynamicMethodsNext);

            if (RegularConfig.linkMode.equals("strict")) {
                for (Fragment freeStateFragment : toDelete) {
                    HashSet<Fragment> addSinkFragments = dataflowDetect.linkFreeStateFragments(freeStateFragment);
for (Fragment newSinkFragment : addSinkFragments) { // TODO: Add switch to select whether to enable heuristic selection
                        flushSinkFragmentsBasedOnPriority(newSinkFragment, allSinkFragments, newSinkFragments);
                    }
                }
                FragmentsContainer.sinkFragments = new HashSet<>(newSinkFragments);
            }
            freeStateFragments.removeAll(toDelete);

// // If you have not exited, calculate and evaluate the priority of Fragments\
// DataFlowAnalysisUtils.calculatePriority(newSinkFragments, allSinkFragments);
        }
        FragmentsContainer.sinkFragments = allSinkFragments;

        newSinkFragments.clear();
        for (Fragment sourceFragment : FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.SOURCE)) {
            if (!RuleUtils.heuristicGadgetChainLink(sourceFragment, null))
                continue;
            HashSet<Fragment> addSinkFragments = dataflowDetect.linkSourceFragments(sourceFragment);
            for (Fragment fragment : addSinkFragments) {
                flushSinkFragmentsBasedOnPriority(fragment, newSinkFragments, newSinkFragments);
            }

            FragmentsContainer.gadgetFragments = newSinkFragments;
        }

        FragmentsContainer.sortSinkFragments();
        log.info("Total number of Gadget chains = " + FragmentsContainer.gadgetFragments.size());
    }

    /**
     * 对检测出的 gadget Fragments 收集信息, 生成 IOCD
     */
    public static void buildIOCD() throws Exception {
        BasicDataContainer.stage = Stage.IOCD_GENERATING;

        setDetectSchemeOn();
        int count = 0, detectedCount = 0;

        Instruments instruments = new Instruments();
// First check whether the target storage directory of the result exists, and if it does not exist, create it
        String targetResultsPath = RegularConfig.outputDir + File.separator + "gadgets" + File.separator + RegularConfig.outPutDirName + File.separator;
        DataSaveLoadUtil.createDir(targetResultsPath);

        for (HashSet<Fragment> sinkFragments : FragmentsContainer.sortedSinkFragmentsMap.values()) {
            for (Fragment sinkFragment : sinkFragments) {
                if (!RuleUtils.heuristicFilterGF(sinkFragment, detectedCount))
                    continue;
                detectedCount++;
                log.info("[Generating IOCD]");
                DataSaveLoadUtil.recordCallStackToFile(sinkFragment.gadgets, sinkFragment.sinkType,
                        RegularConfig.outputDir + "/gadgets/interInfos/" + sinkFragment.sinkType.toString() + "SinkFragments.txt",
                        true);
                GadgetInfoRecord gadgetInfoRecord = FragmentsContainer.generateInitGadgetInfoRecord(sinkFragment);

                if (gadgetInfoRecord != null) {
                    inferGadgetsInfos(gadgetInfoRecord);
                    if (gadgetInfoRecord.flag)
                        count++;
                    try {
                        constructIOCDAndSave(gadgetInfoRecord, instruments);
                    } catch (Throwable throwable) {
                        throwable.printStackTrace();
                    }
                } else if (gadgetInfoRecord == null) {
                    System.out.println("[Pass Gadget Chain Collection]");
                }
            }
        }

        log.info("Number of gadget chains successfully generated for IOCD = " + count);

// Finally output the insert information
        exportInstrumentsRecordJson(instruments, RegularConfig.outputDir + File.separator + "gadgets" + File.separator + RegularConfig.outPutDirName + File.separator);
    }

    public static void inferGadgetsInfos(GadgetInfoRecord gadgetInfoRecord) {
        SootMethod sourceGadget = gadgetInfoRecord.gadgets.getFirst();
        MethodDescriptor descriptor = initDealBeforeInferring(gadgetInfoRecord);

        LinkedList<SootMethod> callStack = new LinkedList<>();
        callStack.add(sourceGadget);

        try {
            new TimeOutTask() {
                @Override
                protected void task() throws IOException {
                    dataflowDetect.inferGadgetInfosOfWholeLife(sourceGadget, gadgetInfoRecord, callStack);
                }

                @Override
                protected void timeoutHandler() {
                    log.error("Timeout when analyzing method" + sourceGadget.getName() + ". Located in class"
                            + sourceGadget.getDeclaringClass());
                }
            }.run(timeThread);
        } catch (Throwable e) {
            e.printStackTrace();
            descriptor.isEntry = false;
            return;
        }
    }

    public static void constructIOCDAndSave(GadgetInfoRecord gadgetInfoRecord, Instruments instruments) throws Exception {
        if (!gadgetInfoRecord.flag)
            return;
        if (gadgetInfoRecord.hashCollisionReview == 1) {
            if (!RuleUtils.recordCollisionForSingleHC(gadgetInfoRecord.linkedFragments,
                    RuleUtils.getEqFragmentByIndex(gadgetInfoRecord.linkedFragments, 1), gadgetInfoRecord))
                return;
        }
        if (gadgetInfoRecord.hashCollisionReview == 0) {
            HashSet<SootField> rootFieldsRecord = new HashSet<>();
            for (ClassNode classNode : gadgetInfoRecord.classFieldsGraph.values()) {
                if (classNode.source == null)
                    continue;
                if (!classNode.source.isField())
                    continue;

                if (!rootFieldsRecord.contains(classNode.source.field.getFirst()))
                    rootFieldsRecord.add(classNode.source.field.getFirst());
                else {
                    gadgetInfoRecord.flag = false;
                    return;
                }
            }
        }

        String dir = RegularConfig.outputDir + "/gadgets" + File.separator + RegularConfig.outPutDirName + File.separator;
        exportGadgetRecordJson(gadgetInfoRecord, dir);
        recordIfStmtAndMethodForInst(gadgetInfoRecord, instruments);
    }

}
