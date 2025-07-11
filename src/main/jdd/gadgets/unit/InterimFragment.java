package jdd.gadgets.unit;

import jdd.tranModel.Taint.Taint;
import callgraph.cfg.Node;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import soot.SootMethod;
import jdd.util.ClassRelationshipUtils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;


public class InterimFragment {
    public boolean flag = true;
    public SootMethod head;
    public Node invokedNode;
// Record the call stack, starting from head to implement a specific method;
    public LinkedList<SootMethod> callStack = new LinkedList<>();
    public HashSet<SootMethod> preLinkableMethods = new HashSet<>();

    public HashMap<Integer, HashSet<SourceNode>> taintSourceActions = new HashMap<>();

    public InterimFragment(SootMethod head,
                           MethodDescriptor descriptor){
        this.head = head;
        init(descriptor);
    }

    public void init(MethodDescriptor descriptor){
        for (SootMethod superMtd: ClassRelationshipUtils.getAllSuperMethods(head, true)){
            if (superMtd.isConcrete()
                    | !(FragmentsContainer.searched.contains(head) | FragmentsContainer.sources.contains(head)))
                continue;

            preLinkableMethods.add(superMtd);
        }

        if (preLinkableMethods.isEmpty()) {
            flag = false;
            return;
        }

        if (!descriptor.retTainted.isEmpty() & descriptor.returnStmt != null) {
            HashSet<SourceNode> retTaintAction = new HashSet<>();
            for (Taint taint: descriptor.retTainted){
                for (SourceNode sourceNode: descriptor.sourcesTaintGraph.matchTaintedSources(taint)){
                    if (!sourceNode.isConstant())
                        retTaintAction.add(sourceNode);
                }
            }
            taintSourceActions.put(-1,retTaintAction);
        }

        HashMap<Integer, HashSet<SourceNode>> paramSourceNodesMap = new HashMap<>();
        for (SourceNode from: descriptor.sourcesTaintGraph.sourcesInfluenceRecord.keySet()){
            SourceNode to = descriptor.sourcesTaintGraph.sourcesInfluenceRecord.get(from);

            if (from.isParameter() & !to.isConstant()) {
                if (!paramSourceNodesMap.containsKey(from.ind))
                    paramSourceNodesMap.put(from.ind, new HashSet<>());
                paramSourceNodesMap.get(from.ind).add(to);
            }
        }

        for (int ind: paramSourceNodesMap.keySet())
            taintSourceActions.put(ind, paramSourceNodesMap.get(ind));

        if (taintSourceActions.isEmpty())
            flag = false;
    }
}
