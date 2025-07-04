package jdd.gadgets.unit;

import soot.SootClass;
import jdd.tranModel.Rules.RuleUtils;
import callgraph.cfg.Node;
import jdd.config.RegularConfig;
import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import lombok.Getter;
import lombok.Setter;
import jdd.markers.SinkType;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import jdd.tranModel.TransformableNode;
import jdd.util.ClassRelationshipUtils;
import callgraph.utilClass.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import static jdd.tranModel.Rules.RuleUtils.sanitizerArrayElement;
import static jdd.dataflow.DataFlowAnalysisUtils.shortPriorityLinkCheck;
import static jdd.util.ClassRelationshipUtils.isValidSuperAbstractOrInterfaceMethod;

/**
 * Fragment data structure
 */

@Getter
@Setter
public class Fragment {
boolean flag = true; // Identify the legality of the Fragment. If flag==false, remove the Fragment
    public enum FRAGMENT_STATE{SOURCE, FREE_STATE, SINK}
    public FRAGMENT_STATE state = null;
public enum FRAGMENT_TYPE{POLYMORPHISM, DYNAMIC_PROXY, REFLECTION} // Follow up on head judgment
    public FRAGMENT_TYPE type = null;

    public SinkType sinkType = null;

public SootMethod head = null; // Start method, record the specific implementation

public SootMethod end = null; // Dynamic method call, the recorded call method has taken into account the pointer analysis results

    public HashSet<SootMethod> endInvokableMethods = null;

    public TransformableNode invokeNode = null;
    public LinkedList<SootMethod> gadgets = new LinkedList<>();

    public HashMap<Integer, HashSet<HashSet<Integer>>> endToHeadTaints = new HashMap<>();

    public ConnectRequire connectRequire = null;

    public int priority = 1;

public LinkedList<Integer> linkedFragments = new LinkedList<>(); // Sequential record
    public LinkedList<SootMethod> linkedDynamicMethods = new LinkedList<>();

    private Fragment(Fragment fragment){
        this.flag = fragment.flag;
        this.state = fragment.state;
        this.type = fragment.type;
        this.sinkType = fragment.sinkType;
        this.head = fragment.head;
        this.end = fragment.end;
        this.endInvokableMethods = new HashSet<>(fragment.endInvokableMethods);
        this.invokeNode = fragment.invokeNode;
        this.gadgets = new LinkedList<>(fragment.gadgets);
        this.endToHeadTaints = new HashMap<>(fragment.endToHeadTaints);
        this.connectRequire = fragment.connectRequire;
        this.priority = fragment.priority;
        this.linkedFragments = new LinkedList<>(fragment.linkedFragments);
        this.linkedDynamicMethods = new LinkedList<>(fragment.linkedDynamicMethods);
    }

    public Fragment(MethodDescriptor descriptor, LinkedList<SootMethod> chain,
                    SootMethod invokeMtd, TransformableNode invokeNode,
                    HashSet<SootMethod> endInvokableMethods) {

        gadgets = new LinkedList<>(chain);
        head = chain.get(0);
        this.invokeNode = invokeNode;
        this.end = invokeMtd;
        if (endInvokableMethods != null)
            this.endInvokableMethods = endInvokableMethods;
        init(descriptor);

        if (flag){
            FragmentsContainer.basicFragmentsMap.put(this.hashCode(), this);
        }
    }

    public Fragment(Fragment preFragment, Fragment sucFragment){
        boolean isEqualsConnectFlag = false;
        if (RuleUtils.isEqMethod(preFragment.head)
                && RuleUtils.isEqMethod(sucFragment.head)){
            if (!RuleUtils.isValidEqualsConnect(preFragment,sucFragment)){
                flag = false;
                return;
            }
            isEqualsConnectFlag = true;
        }
        if (!isEqualsConnectFlag) {
            if (!shortPriorityLinkCheck(preFragment, sucFragment)) {
                flag = false;
                return;
            }
        }

        HashSet<HashSet<Integer>> paramsTaintRequires = RuleUtils.linkCheckOfTaints(preFragment, sucFragment);
        if (paramsTaintRequires.isEmpty()){
            flag = false;
            return;
        }else if (paramsTaintRequires.size() == 1
                & preFragment.gadgets.getFirst().getSubSignature().equals("boolean equals(java.lang.Object)")){
            HashSet<Integer> requires = paramsTaintRequires.iterator().next();
            if (requires.isEmpty())
                requires.add(0);
        }

        this.connectRequire = new ConnectRequire(paramsTaintRequires, preFragment.connectRequire.preLinkableMethods);
        this.connectRequire.dynamicProxyLinkCheck = preFragment.connectRequire.dynamicProxyLinkCheck;
        this.connectRequire.reflectionCheck = preFragment.connectRequire.reflectionCheck;


        type = sucFragment.type;
        sinkType = sucFragment.sinkType;


        LinkedList<SootMethod> gadgets = new LinkedList<>(preFragment.gadgets);
        gadgets.addAll(sucFragment.gadgets);
        this.gadgets = gadgets;


        head = preFragment.head;
        end = sucFragment.end;
        invokeNode = sucFragment.invokeNode;
        state = preFragment.state;


        LinkedList<Integer> tmpLinkedFragments = new LinkedList<>(sucFragment.linkedFragments);
        tmpLinkedFragments.addFirst(preFragment.hashCode());
        linkedFragments.addAll(new LinkedList<>(tmpLinkedFragments));

        linkedDynamicMethods.add(preFragment.end);
        linkedDynamicMethods.addAll(sucFragment.linkedDynamicMethods);

        if (flag){
            for (HashSet<Integer> condSet: paramsTaintRequires){
                if (!FragmentsContainer.paramsTaintRequireSinkFragmentsMap.containsKey(condSet))
                    FragmentsContainer.paramsTaintRequireSinkFragmentsMap.put(condSet, new HashSet<>());
                FragmentsContainer.paramsTaintRequireSinkFragmentsMap.get(condSet).add(this);
            }
        }
    }

    private void init(MethodDescriptor descriptor){
        assert head != null & end != null;

        if (!validFragmentCheck())
            return;

        if (FragmentsContainer.protocolCheckRule.isSource(head)){
            state = FRAGMENT_STATE.SOURCE;
        }
        else if (FragmentsContainer.isSinkMethod(end)) {
            state = FRAGMENT_STATE.SINK;
            linkedFragments.add(this.hashCode());
        }

        initForPolymorphism(descriptor);
        recordProxyRequires(descriptor);
    }

    public Fragment copy(Fragment fragment){
        return new Fragment(fragment);
    }

    public void initForPolymorphism(MethodDescriptor descriptor){
        if (!RuleUtils.isValidEqualsMethod(head, end, state)){
            flag = false;
            return;
        }

        HashSet<SootMethod> preLinkableMethods = new HashSet<>();
        if (state == null || FRAGMENT_STATE.SINK.equals(state)) {
            for (SootMethod superMethod : ClassRelationshipUtils.getAllSuperMethods(head, false)) {
                if (!ClassRelationshipUtils.isDynamicMethod(superMethod)) continue;
                preLinkableMethods.add(superMethod);
            }
        }

        HashSet<SootMethod> toDelete = new HashSet<>();
        for (SootMethod mtd1: preLinkableMethods){
            for (SootMethod mtd2: preLinkableMethods){
                if (mtd1.equals(mtd2))
                    continue;
                if (!mtd1.getSubSignature().equals(mtd2.getSubSignature()))
                    continue;

                if (ClassRelationshipUtils.isSubClassOf(mtd1.getDeclaringClass(), mtd2.getDeclaringClass()))
                    toDelete.add(mtd1);
            }
        }
        preLinkableMethods.removeAll(toDelete);

        this.connectRequire = new ConnectRequire(preLinkableMethods);

        if (state == null) {
            if (!connectRequire.preLinkableMethods.isEmpty())
                state = FRAGMENT_STATE.FREE_STATE;
            else {
                flag = false;
                return;
            }
        }

// Set type
        if (state.equals(FRAGMENT_STATE.SOURCE)) {
            if (RegularConfig.protocol.equals("json"))
                type = FRAGMENT_TYPE.REFLECTION;
            else
                type = null;
        }
        else if (BasicDataContainer.commonMtdMap.get("invokeHandler").getSubSignature().equals(head.getSubSignature()))
type = FRAGMENT_TYPE.DYNAMIC_PROXY; // contains POLYMORPHISM
        else if (!preLinkableMethods.isEmpty())
            type = FRAGMENT_TYPE.POLYMORPHISM;
        else flag = false;

        if (!flag)
            return;

        if (!state.equals(FRAGMENT_STATE.SINK) & !state.equals(FRAGMENT_STATE.SOURCE)){
            if (gadgets.size() > BasicDataContainer.polyLenLimit){
                flag = false;
                return;
            }
        }
        setTaintsDependence(descriptor, invokeNode.node);
    }

    public void initForDynamicProxy(MethodDescriptor descriptor){

    }

    public SootClass getClassForHead(){
        SootClass headClz = head.getDeclaringClass();
        if (gadgets.size() < 2) return headClz;
        SootClass nextClz = gadgets.get(1).getDeclaringClass();
        if (ClassRelationshipUtils.isSubClassOf(nextClz, headClz)
                && nextClz.getMethodUnsafe(head.getSubSignature()) == null)
            return nextClz;

        return headClz;
    }

    /**
     * Currently, simplified processing method is adopted: Fragment(Proxy) head->end
     */
    public void recordProxyRequires(MethodDescriptor descriptor){
        if (!ClassRelationshipUtils.isProxyMethod(head))
            return;
        if (!state.equals(FRAGMENT_STATE.SINK)){
            flag = false;
            return;
        }

        extractProxyInfos(descriptor);
    }

    public void extractProxyInfos(MethodDescriptor descriptor){
        TransformableNode nextTfNode = RecordUtils.findTfNodeToNextMtd(descriptor, gadgets);

        HashSet<Integer> path_record = nextTfNode.path_record;
        for (Integer hashCode : path_record){
            if (path_record.contains(-hashCode))
                continue;

            TransformableNode addIfStmt = TransformableNode.ifStmtHashMap.get(hashCode > 0 ? hashCode:-hashCode);
            if (addIfStmt == null)  continue;
// The necessary condition branch hashCode is used to facilitate subsequent branch sensitive verification
            connectRequire.condSet.add(hashCode);
// RecordUtils.extractMethodName(nextTfNode, descriptor);
        }
    }

    /**
     * Add taint dependency between head method's params and the subsequent method's params
     * @param descriptor
     * @param invokeNode
     */
    public void setTaintsDependence(MethodDescriptor descriptor, Node invokeNode){
// MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(this.invokeNode.method);
// descriptor = BasicDataContainer.getOrCreateDescriptor(gadgets.getLast());
        assert descriptor != null;

        ValueBox thisValueBox = Parameter.getThisValueBox(invokeNode);
        if (thisValueBox != null){
            if (Utils.isTainted(thisValueBox.getValue(), descriptor.taints)) {
                if (sanitizerArrayElement(descriptor, thisValueBox)){
                    flag = false;
                    return;
                }
                HashSet<Integer> conParams = Utils.getEndToHeadTaintsCon(descriptor, thisValueBox.getValue());
                addEndToHeadTaints(-1, conParams);
            }
        }

        InvokeExpr invokeExpr = ((Stmt) invokeNode.unit).getInvokeExpr();
        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            Value argValue = invokeExpr.getArg(ind);
            if (Utils.isTainted(argValue, descriptor.taints)) {
                HashSet<Integer> conParams = Utils.getEndToHeadTaintsCon(descriptor, argValue);
                addEndToHeadTaints(ind, conParams);
            }
        }
    }


    public void addEndToHeadTaints(int ind, HashSet<Integer> conParms){
        if (!endToHeadTaints.containsKey(ind)) {
            endToHeadTaints.put(ind, new HashSet<>());
            endToHeadTaints.get(ind).add(conParms);
            return;
        }

        HashSet<HashSet<Integer>> toDelete = new HashSet<>();
        boolean addFlag = true;
        for (HashSet<Integer> recordedConParams: endToHeadTaints.get(ind)){
            if (recordedConParams.containsAll(conParms) & recordedConParams.size() > conParms.size())
                toDelete.add(recordedConParams);
            else if (conParms.containsAll(recordedConParams))
                addFlag = false;
        }

        endToHeadTaints.get(ind).removeAll(toDelete);
        if (addFlag)
            endToHeadTaints.get(ind).add(conParms);
    }

    public boolean validFragmentCheck(){
        boolean isValid = true;
        if (head.getSubSignature().equals(end.getSubSignature())){
            if (RuleUtils.isEqMethod(end)){
                if (!FragmentsContainer.isSingleFixedEqualsMethod(head))
                    isValid=false;
            }
            else if (endInvokableMethods == null
                    || !isValidSuperAbstractOrInterfaceMethod(head, end)){
                isValid = false;
            }
        }
        if (!isValid){
            this.flag = false;
            return false;
        }

        return true;
    }

    public boolean equals(Object object){
        if (!(object instanceof Fragment))
            return false;

        Fragment fragment = (Fragment) object;
        return gadgets.equals(fragment.gadgets) & end.equals(fragment.end);
    }

    public void calPrioritySimply(){
        priority = linkedFragments.size() + gadgets.size();
    }

}
