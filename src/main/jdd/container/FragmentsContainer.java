package jdd.container;

import callgraph.utilClass.StaticAnalyzeUtils.ClassUtils;
import callgraph.utilClass.StaticAnalyzeUtils.FieldUtil;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.PointToAnalyze.pointer.Pointer;
import jdd.config.RegularConfig;
import jdd.config.SootConfig;
import jdd.dataflow.DataFlowAnalysisUtils;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.unit.Fragment;
import jdd.gadgets.unit.InterimFragment;
import jdd.markers.SinkType;
import jdd.markers.Stage;
import jdd.rules.protocol.AbstractProtocolCheckRule;
import jdd.rules.protocol.HessianProtocolCheckRule;
import jdd.rules.protocol.JdkNativeProtocolCheckRule;
import jdd.rules.protocol.JsonProtocolCheckRule;
import jdd.rules.sinks.CheckRule;
import jdd.tranModel.Rules.RuleUtils;
import jdd.tranModel.Taint.Taint;
import jdd.tranModel.TransformableNode;
import jdd.util.ClassRelationshipUtils;
import jdd.util.Utils;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.Stmt;

import java.io.IOException;
import java.util.*;

import static jdd.dataflow.DataFlowAnalysisUtils.serializableIntercept;
import static jdd.detector.SearchUtils.setDetectSchemeOff;
import static jdd.detector.SearchUtils.setDetectSchemeOn;
import static jdd.gadgets.unit.Fragment.FRAGMENT_STATE.SINK;
import static jdd.gadgets.unit.Fragment.FRAGMENT_STATE.SOURCE;
import static jdd.tranModel.Rules.RuleUtils.detectAndRecordHashCollision;
import static jdd.util.ClassRelationshipUtils.isDynamicMethod;

@Slf4j
public class FragmentsContainer {
    public static AbstractProtocolCheckRule protocolCheckRule = null;
    public static HashMap<SootClass, HashSet<SourceNode>> fixedHashClass = new HashMap<>();
    public static HashSet<SootClass> singleHashFixedClass = new HashSet<>();
    public static HashMap<SootClass, HashSet<SourceNode>> classHashCodeFieldsMap = new HashMap<>();
    public static HashSet<SootMethod> searched = new HashSet<>();
    public static HashSet<SootMethod> sources = new HashSet<>();
    public static HashMap<Integer, Fragment> basicFragmentsMap = new HashMap<>();
    public static HashMap<Fragment.FRAGMENT_STATE, LinkedHashSet<Fragment>> stateFragmentsMap = new HashMap<>();
    public static HashMap<Fragment.FRAGMENT_TYPE, LinkedHashSet<Fragment>> typeFragmentsMap = new HashMap<>();
    public static TreeMap<Integer, HashSet<Fragment>> sortedSinkFragmentsMap = new TreeMap<>();
    public static HashSet<Fragment> sinkFragments = new HashSet<>();
    public static HashSet<InterimFragment> interimFragments = new HashSet<>(); // TODO: Add a stored record

    public static HashMap<HashSet<Integer>, HashSet<Fragment>> paramsTaintRequireSinkFragmentsMap = new HashMap<>();
    public static HashSet<Fragment> gadgetFragments = new HashSet<>();

    public static HashMap<SootMethod, HashSet<SootMethod>> dynSubMtdsMap = new HashMap<>();
    // map super method -> sub class
    public static HashMap<SootMethod, HashSet<SootClass>> superMtdSources = new HashMap<>();
    // When segmented detection, it is used to handle the situation where mtd-> calls the parent class method
    public static HashSet<SootMethod> dynamicMtds = new HashSet<>();
    public static HashSet<Fragment> dynamicProxyFragments = new HashSet<>();

    public static HashMap<Fragment, GadgetInfoRecord> gadgetInfoRecordMap = new HashMap<>();

    public static void init() throws IOException {
        if (RegularConfig.protocol.equals("jdk")) {
            protocolCheckRule = new JdkNativeProtocolCheckRule();
        } else if (RegularConfig.protocol.equals("hessian")) {
            protocolCheckRule = new HessianProtocolCheckRule();
        } else if (RegularConfig.protocol.equals("json")) {
            protocolCheckRule = new JsonProtocolCheckRule();
        }

        long startTime = System.currentTimeMillis(), endTime1, endTime2;
        protocolCheckRule.init();
        sources = new HashSet<>(protocolCheckRule.getSourceMethods());
log.info("Source Methods Number = " + sources.size());

// Load CG
        SootConfig.constructCG();
        endTime1 = System.currentTimeMillis();
log.info("[Call Graph build time]"); // It is not currently calculated within the total detection time
        Utils.printTimeConsume(endTime1, startTime);

        if (!RegularConfig.protocol.equals("json")
                & !RegularConfig.derivationType.equals("SecondDesDerivation")
                & !RegularConfig.derivationType.equals("InvokeDerivation")) {
            setDetectSchemeOn(); // Set the flag to start detection
            protocolCheckRule.filterFixedEqualsMethods();
            setDetectSchemeOff(); // Set the flag to start detection
        }

// Initialize the storage structure
        for (Fragment.FRAGMENT_STATE state : Fragment.FRAGMENT_STATE.values())
            stateFragmentsMap.put(state, new LinkedHashSet<>());
        for (Fragment.FRAGMENT_TYPE type : Fragment.FRAGMENT_TYPE.values())
            typeFragmentsMap.put(type, new LinkedHashSet<>());

// For dynamic proxy fragments (this part requires a lightweight path sensitivity) TODO: Not yet incorporated
// generateInvocationHandlerFragments();
    }

    public static void reset() {
        sources = new HashSet<>();
        searched = new HashSet<>();

        basicFragmentsMap = new HashMap<>();
        sortedSinkFragmentsMap = new TreeMap<>();
        sinkFragments = new HashSet<>();
        interimFragments = new HashSet<>();
        gadgetFragments = new HashSet<>();
        dynamicMtds = new HashSet<>();
        dynSubMtdsMap = new HashMap<>();
        gadgetInfoRecordMap = new HashMap<>();
    }

    public static boolean isSinkMethod(SootMethod sootMethod) {
        for (CheckRule checkRule : protocolCheckRule.sinkCheckRule.values()) {
            if (checkRule.isSinkMethod(sootMethod))
                return true;
        }
        return false;
    }


    public static Fragment getFragment(LinkedList<SootMethod> callStack,
                                       SootMethod invokedMethod) {
        for (Fragment.FRAGMENT_STATE state : stateFragmentsMap.keySet()) {
            for (Fragment recordedFragment : stateFragmentsMap.get(state)) {
                if (Utils.listEqual(recordedFragment.getGadgets(), callStack)
                        & invokedMethod.equals(recordedFragment.end))
                    return recordedFragment;
            }
        }
        return null;
    }

    public static boolean isFixedEqualsMethod(SootMethod sootMethod) {
        if (sootMethod == null)
            return false;
        return RuleUtils.isEqMethod(sootMethod)
                && FragmentsContainer.fixedHashClass.containsKey(sootMethod.getDeclaringClass());
    }

    public static boolean isSingleFixedEqualsMethod(SootMethod sootMethod) {
        if (sootMethod == null)
            return false;
        return RuleUtils.isEqMethod(sootMethod)
                && FragmentsContainer.singleHashFixedClass.contains(sootMethod.getDeclaringClass());
    }

    public static HashSet<Fragment> getLinkableSinkFragments(Fragment freeStateFragment) {
        HashSet<Fragment> ret = new HashSet<>();
        SootMethod callerMethod = freeStateFragment.end;
        for (Fragment recordedSinkFragment : sinkFragments) {
            if (recordedSinkFragment.head.equals(freeStateFragment.head))
                continue;
            if (recordedSinkFragment.connectRequire.preLinkableMethods.contains(callerMethod)) {
                if (freeStateFragment.endInvokableMethods != null) {
                    if (!freeStateFragment.endInvokableMethods.contains(recordedSinkFragment.head))
                        continue;
                }
                ret.add(recordedSinkFragment);
            }
        }
        return ret;
    }

    /**
     * Check if sinkFragments has a fragment whose head method is in endInvokable methods and is in the preLinkable Methods of dynamic Method
     * @param dynamicMethod
     * @param endInvokableMethods
     * @return
     */
    public static HashSet<Fragment> getLinkableSinkFragments(SootMethod dynamicMethod, HashSet<SootMethod> endInvokableMethods) {
        HashSet<Fragment> ret = new HashSet<>();
        for (Fragment recordedSinkFragment : sinkFragments) {
            if (recordedSinkFragment.connectRequire.preLinkableMethods.contains(dynamicMethod)) {
                if (endInvokableMethods != null) {
                    if (!endInvokableMethods.contains(recordedSinkFragment.head))
                        continue;
                }
                ret.add(recordedSinkFragment);
            }
        }
        return ret;
    }

    public static HashSet<Fragment> getSinkFragmentsByHead(SootMethod head) {
        HashSet<Fragment> ret = new HashSet<>();
        for (Fragment recordedFragment : sinkFragments) {
            if (recordedFragment.head.equals(head))
                ret.add(recordedFragment);
        }

        return ret;
    }

    public static HashSet<Fragment> getSinkFragmentByEnd(SootMethod end) {
        HashSet<Fragment> ret = new HashSet<>();
        for (Fragment recordedFragment : sinkFragments) {
            if (recordedFragment.end.equals(end))
                ret.add(recordedFragment);
        }

        return ret;
    }

    /**
     * generate Fragments
     * @param descriptor
     * @param callStack
     * @param invokedMethod
     * @param tfNode
     * @param endInvokableMethods
     * @param isSinkFlag
     * @return
     */
    public static HashSet<Fragment> generateFragments(MethodDescriptor descriptor,
                                                      LinkedList<SootMethod> callStack,
                                                      SootMethod invokedMethod,
                                                      TransformableNode tfNode,
                                                      HashSet<SootMethod> endInvokableMethods,
                                                      boolean isSinkFlag) {
        assert invokedMethod != null & tfNode.containsInvoke();
        HashSet<Fragment> newSinkFragments = new HashSet<>();

        if (!(BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING) || BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE))
                || (!protocolCheckRule.openBPLink() && !isSinkFlag))
            return newSinkFragments;

        if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE) && !isSinkFlag) return newSinkFragments;

        if (RuleUtils.isInvalidFragmentEnd(invokedMethod, isSinkFlag))
            return newSinkFragments;


        Fragment recordedFragment = getFragment(callStack, invokedMethod);

// MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(callStack.getLast());
        if (((Stmt) tfNode.node.unit) instanceof AssignStmt) {
            Value retValue = Parameter.getReturnedValue(tfNode.node);
            Taint newTaint = descriptor.getOrCreateTaint(retValue, new LinkedList<>());
            RuleUtils.addTaint(descriptor, newTaint);
        }

// There is no same/related record fragment
        if ((recordedFragment == null && (!invokedMethod.isConcrete()
                || BasicDataContainer.isValidHeadOfObjectMethod(invokedMethod))
                && !invokedMethod.isFinal()) || isSinkFlag) {

            if (BasicDataContainer.openChainedSinkCheck) {
                newSinkFragments = generateChainedInvokeFragments(descriptor, callStack, invokedMethod, tfNode, endInvokableMethods);
                if (!newSinkFragments.isEmpty())
                    return newSinkFragments;
            }

            if (!RuleUtils.isEndMtdControllableHC(descriptor, tfNode, callStack)) return newSinkFragments;

            endInvokableMethods = getInvokableMethods(descriptor, tfNode, invokedMethod, endInvokableMethods);
            Fragment fragment = new Fragment(descriptor, callStack, invokedMethod, tfNode, endInvokableMethods);

            if (fragment.isFlag())
                newSinkFragments.add(fragment);
            updateFragments(fragment);
            return newSinkFragments;
        } else if (recordedFragment != null) {
            if (!recordedFragment.invokeNode.equals(tfNode.node)) {
                recordedFragment.setTaintsDependence(descriptor, tfNode.node);
            }
        }

        return newSinkFragments;
    }


    public static HashSet<SootMethod> getInvokableMethods(MethodDescriptor descriptor,
                                                          TransformableNode tfNode,
                                                          SootMethod invokedMethod,
                                                          HashSet<SootMethod> endInvokableMethods) {
        if (endInvokableMethods != null && !endInvokableMethods.isEmpty())
            return endInvokableMethods;

        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox != null) {
            Pointer thisPointer = descriptor.pointTable.getPointer(thisValueBox.getValue());
            if (thisPointer == null)
                return endInvokableMethods;

            SootClass pointerClz = Utils.toSootClass(thisPointer.getType());
            HashSet<SootMethod> ret1 = new HashSet<>();
            if (!pointerClz.equals(invokedMethod.getDeclaringClass())
                    && ClassRelationshipUtils.isSubClassOf(pointerClz, invokedMethod.getDeclaringClass())) {
                ret1 = DataFlowAnalysisUtils.getInvokedMethods(thisPointer, tfNode, descriptor);
            }

            if (!thisPointer.getExtraTypes().isEmpty()) {
                HashSet<SootClass> extraClasses = new HashSet<>();
                for (Type type : thisPointer.getExtraTypes()) {
                    extraClasses.add(Utils.toSootClass(type));
                }
                HashSet<SootMethod> ret = new HashSet<>();
                for (SootMethod invokableMtd : ClassRelationshipUtils.getAllSubMethods(invokedMethod)) {
                    boolean flag = true;
                    SootClass invokedMtdClass = invokableMtd.getDeclaringClass();
                    for (SootClass extraClass : extraClasses) {
                        if (!ClassRelationshipUtils.isSubClassOf(invokedMtdClass, extraClass)) {
                            flag = false;
                            break;
                        }
                    }

                    if (flag)
                        ret.add(invokableMtd);
                }

                ret.retainAll(ret1);
                return ret;
            }

            if (!ret1.isEmpty())
                return ret1;
        }

        return endInvokableMethods;
    }

    /**
     * Update fragments' field including dynamic methods, dynamic submethods and sources and add fragment to collection
     * @param fragment
     */
    public static void updateFragments(Fragment fragment) {
        SootMethod invokedMethod = fragment.end;

        if (fragment.isFlag()) {
            stateFragmentsMap.get(fragment.state).add(fragment);
            if (fragment.type != null)
                typeFragmentsMap.get(fragment.type).add(fragment);
            if (fragment.state.equals(SINK)) {
                sinkFragments.add(fragment);
            }

            SootMethod invokedSuperMethod = ClassRelationshipUtils.getTopSuperMethod(invokedMethod);
            if (isDynamicMethod(invokedMethod) && !dynamicMtds.contains(invokedSuperMethod)) {
                HashSet<SootMethod> subMethods = ClassRelationshipUtils.getAllSubMethods(invokedSuperMethod);
                HashSet<SootMethod> toDelete = new HashSet<>();
                for (SootMethod tmpMethod : subMethods) {
                    if (searched.contains(tmpMethod)) toDelete.add(tmpMethod);
                    if (BasicDataContainer.blackList.contains(tmpMethod.getSignature()))
                        continue;
                    MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(fragment.invokeNode.method);
                    if (!tmpMethod.isConcrete() || (BasicDataContainer.needSerializable
                            && serializableIntercept(descriptor, tmpMethod, fragment.invokeNode, fragment.gadgets))) {
                        toDelete.add(tmpMethod);
                        continue;
                    }
                }

                if (RuleUtils.isEqMethod(invokedMethod)) {
                    for (SootMethod tmpMethod : subMethods) {
                        if (!FragmentsContainer.isFixedEqualsMethod(tmpMethod))
                            toDelete.add(tmpMethod);
                    }
                }
                subMethods.removeAll(toDelete);

                dynamicMtds.add(invokedSuperMethod);
                dynSubMtdsMap.put(invokedSuperMethod, subMethods);

                sources.addAll(subMethods);
            }
        }
    }

    /**
     * Add all subclasses that called the super method to superMtdSources
     * @param mtd
     * @param nextMtds
     */
    public static void searchMtdForSubClass(SootMethod mtd, HashSet<SootMethod> nextMtds) {
        if (superMtdSources.containsKey(mtd))
            return;
        if (!needSearchMtdForSubClass(mtd))
            return;
        SootClass clz = mtd.getDeclaringClass();
        HashSet<SootClass> passClass = new HashSet<>();
        HashSet<SootClass> nextMtdClz = new HashSet<>();
        nextMtds.forEach(item -> nextMtdClz.add(item.getDeclaringClass()));

        for (SootClass subClz : ClassUtils.getAllSubs_BFS(clz)) {
            if (subClz.equals(clz) || !nextMtdClz.contains(subClz))
                continue;
            if (!FragmentsContainer.protocolCheckRule.candidateClassSet.contains(subClz))
                continue;
            if (!passClass.isEmpty()) {
                HashSet<SootClass> superClzs = ClassUtils.getAllSupers(subClz);
                superClzs.retainAll(passClass);
                if (!superClzs.isEmpty())
                    continue;
            }
            if (subClz.getMethodUnsafe(mtd.getSubSignature()) == null) {
                superMtdSources.get(mtd).add(subClz);
            } else passClass.add(subClz);
        }
    }

    // It is only required if this.callee() is included in this method
    public static boolean needSearchMtdForSubClass(SootMethod mtd) {
        if (!superMtdSources.containsKey(mtd)) // Used to save subsequent repeated detection
            superMtdSources.put(mtd, new HashSet<>());
        if (RuleUtils.isGenericType(mtd.getDeclaringClass().getType()))
            return false;

        if (mtd.isStatic() || !mtd.hasActiveBody())
            return false;

        Value thisValue = null;
        for (Unit unit : mtd.retrieveActiveBody().getUnits()) {
            Stmt stmt = (Stmt) unit;
            if (thisValue == null) {
                Integer paramInd = Parameter.tryGetParamIdentifiedInUnit(unit);
                if (paramInd == -1) {
                    thisValue = unit.getDefBoxes().get(0).getValue();
                }
            }
            if (!stmt.containsInvokeExpr())
                continue;

            ValueBox thisValueBox = Parameter.getThisValueBox(stmt);
            if (thisValueBox != null && thisValue != null && thisValueBox.getValue().equals(thisValue)) {
                return true;
            }
        }
        return false;
    }

    public static HashSet<InterimFragment> getInterimFragment(SootMethod invokedMethod) {

        HashSet<InterimFragment> ret = new HashSet<>();
        for (InterimFragment interimFragment : interimFragments) {
            if (interimFragment.preLinkableMethods.contains(invokedMethod))
                ret.add(interimFragment);
        }

        return ret;
    }

    public static void generateInterimFragment(MethodDescriptor descriptor) {
// Check, if it is not a method call in source, it does not need to be created.
        SootMethod head = descriptor.sootMethod;
        if (!searched.contains(head))
            return;

        InterimFragment interimFragment = new InterimFragment(head, descriptor);
        if (interimFragment.flag) {
            interimFragments.add(interimFragment);
        }
    }


    public static void updateSinkFragment(LinkedList<SootMethod> callStack,
                                          SinkType sinkType,
                                          TransformableNode tfNode,
                                          MethodDescriptor descriptor) {
        HashSet<Fragment> fragments = generateFragments(descriptor, callStack, callStack.getLast(), tfNode, null, true);
// For Sink Fragments to set the corresponding sink type
        if (fragments.isEmpty()) return;

        for (Fragment fragment : fragments) {
            fragment.setSinkType(sinkType);


            HashSet<Integer> tmpParamsTaintRequire = new HashSet<>();
            HashMap<TransformableNode, HashSet<SourceNode>> map = descriptor.sinkUnitsRecord.get(sinkType);
            if (map != null) {
                if (map.containsKey(tfNode)) {
                    for (SourceNode sourceNode : map.get(tfNode)) {
                        if (sourceNode.isParameter())
                            tmpParamsTaintRequire.add(sourceNode.ind);
                    }
                }

                fragment.connectRequire.paramsTaintRequire = new HashSet<>();
                fragment.connectRequire.paramsTaintRequire.add(tmpParamsTaintRequire);
                sinkFragments.add(fragment);
                stateFragmentsMap.get(SINK).add(fragment);
                if (!SOURCE.equals(fragment.state)) {
                    typeFragmentsMap.get(fragment.type).add(fragment);
                }
            }
        }
    }


    /**
     * Generate new Sink Fragments for chained Method.invoke type Fragments
     * @param descriptor
     * @param callStack
     * @param invokedMethod
     * @param tfNode
     * @param endInvokableMethods
     * @return Whether chained invoke Fragments were generated
     */
    public static HashSet<Fragment> generateChainedInvokeFragments(MethodDescriptor descriptor, LinkedList<SootMethod> callStack,
                                                                   SootMethod invokedMethod,
                                                                   TransformableNode tfNode,
                                                                   HashSet<SootMethod> endInvokableMethods) {
        HashSet<Fragment> ret = new HashSet<>();
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox == null)
            return ret;

// MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(callStack.getLast());
        HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(thisValueBox.getValue());
        if (sourceNodes.size() != 1)
            return ret;

        SourceNode sourceNode = sourceNodes.iterator().next();
        SootClass classOfField = null;
        boolean flag = false;
        if (sourceNode.isField()) {
            if (sourceNode.field.getLast().getType().toString().contains("[]")) {
                if (!Utils.isBasicType(sourceNode.field.getLast().getType()))
                    flag = true;
            }
        }

        if (!flag)
            return ret;

        classOfField = FieldUtil.getSootFieldType(sourceNode.field.getLast());

        HashSet<Fragment> sinkFragments = getLinkableSinkFragments(invokedMethod, endInvokableMethods);
        for (Fragment recordedSinkFragment : sinkFragments) {
            if (SinkType.INVOKE.equals(recordedSinkFragment.sinkType)
                    & !recordedSinkFragment.end.isStatic()
                    & recordedSinkFragment.gadgets.size() < 3) {
// Determine whether the caller is in chain format

                if (ClassRelationshipUtils.isSubClassOf(
                        recordedSinkFragment.head.getDeclaringClass(), classOfField
                )) {
                    LinkedList<SootMethod> gadgets = new LinkedList<>(callStack);
                    gadgets.addAll(recordedSinkFragment.gadgets);

                    Fragment fragment = new Fragment(descriptor, gadgets, recordedSinkFragment.end,
                            recordedSinkFragment.invokeNode, recordedSinkFragment.endInvokableMethods);
                    if (fragment.isFlag()) {
                        fragment.sinkType = recordedSinkFragment.sinkType;
// Create paramsTaintRequire rules to record forward links. Chain type does not require contamination parameters, and can be directly constructed.
                        fragment.connectRequire.paramsTaintRequire = new HashSet<>();
                        fragment.connectRequire.paramsTaintRequire.add(new HashSet<>());
                        updateFragments(fragment);
                        ret.add(fragment);
                    }
                }
            }
        }
        return ret;
    }


    public static GadgetInfoRecord generateInitGadgetInfoRecord(Fragment sinkFragment) throws IOException {
        if (gadgetInfoRecordMap.containsKey(sinkFragment))
            return gadgetInfoRecordMap.get(sinkFragment);

        GadgetInfoRecord gadgetInfoRecord = new GadgetInfoRecord(sinkFragment, sinkFragment.sinkType);
        LinkedList<Fragment> linkedFragments = new LinkedList<>();
        for (int linkedFragmentIndex = 0; linkedFragmentIndex < sinkFragment.linkedDynamicMethods.size(); linkedFragmentIndex++) {
            Integer hashCode = sinkFragment.linkedFragments.get(linkedFragmentIndex);
            Fragment basicFragment = basicFragmentsMap.get(hashCode);
            if (basicFragment == null)
                return null;

            linkedFragments.add(basicFragment);

            if (Fragment.FRAGMENT_TYPE.DYNAMIC_PROXY.equals(basicFragment.type)) {
                if (linkedFragmentIndex - 1 < 0)
                    return null;

                Fragment preFragment = basicFragmentsMap.get(sinkFragment.linkedFragments.get(linkedFragmentIndex - 1));
                assert gadgetInfoRecord.gadgets.contains(basicFragment.head) & gadgetInfoRecord.gadgets.contains(preFragment.end);
                gadgetInfoRecord.dynamicProxyInvokeRecord.put(preFragment.end, basicFragment.head);
            }
        }
        if (sinkFragment.linkedFragments.size() > 0) {
            Fragment lastFragment = basicFragmentsMap.get(sinkFragment.linkedFragments.getLast());
            if (lastFragment == null)
                return null;
            if (!linkedFragments.contains(lastFragment)) linkedFragments.add(lastFragment);
        }
        if (!detectAndRecordHashCollision(gadgetInfoRecord, linkedFragments)) {
            return null;
        }

        gadgetInfoRecord.linkedFragments = linkedFragments;
        gadgetInfoRecordMap.put(sinkFragment, gadgetInfoRecord);
        return gadgetInfoRecord;
    }

    public static void sortSinkFragments() {
        for (Fragment sinkFragment : gadgetFragments) {
            if (!sortedSinkFragmentsMap.containsKey(sinkFragment.priority))
                sortedSinkFragmentsMap.put(sinkFragment.priority, new HashSet<>());
            sortedSinkFragmentsMap.get(sinkFragment.priority).add(sinkFragment);
        }
    }
}
