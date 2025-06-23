//Encapsulate all Nodes in cfg as TransformableNode
//Record the number of forward nodes of TransformableNode as the entry level when the loop is ringed in the subsequent processing cycle
//Fill the encapsulated TransformableNode into waiting for processing
package jdd.tranModel;
import java.cfg.CFG;
import java.cfg.Node;
import lombok.extern.slf4j.Slf4j;
import soot.jimple.IfStmt;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

@Slf4j
public class TranUtil {

    public static int error_cannot_topological_order = 0;
    public static boolean DEBUG = false;

    /**
     * Given cfg returns a TransformableNode list that is topologically sorted according to the cfg
     * @param cfg
     * @return List<TransformableNode>
     */
    public static List<TransformableNode> getTopologicalOrderedTNodesFromCFG(CFG cfg){

        HashMap<Node, TransformableNode> nodeMapTransformNode = new HashMap<>();
        HashMap<TransformableNode, Integer> transformNodeMapPrecursorSize = new HashMap<>();
        LinkedHashSet<TransformableNode> waiting = new LinkedHashSet<>();
// Step
// Step
// Step
        for(Node node : cfg.allNodes.values()){
// I rewrote the hash method of TransformableNode so that the topology order obtained by multiple executions of the same cfg is consistent
            TransformableNode transformableNode = new TransformableNode(node, cfg.entryPoint);
            transformNodeMapPrecursorSize.put(transformableNode, node.precursorNodes.size());
            nodeMapTransformNode.put(node, transformableNode);
            waiting.add(transformableNode);
        }
//        HashSet<TransformableNode> waiting = new HashSet<>(transformNodeMapPrecursorSize.keySet());
//        List<TransformableNode> waitingList = new LinkedList<>(waiting);
//        Collections.sort(waitingList, );

        List<TransformableNode> ret = new LinkedList<>();
        int topologicalOrderFail = 0;
        boolean cycleFlag = false;
        while(!waiting.isEmpty()){
            int fl = 0;
            for(TransformableNode transformableNode : waiting){
                if(transformNodeMapPrecursorSize.get(transformableNode) == 0){
                    ret.add(transformableNode);
                    waiting.remove(transformableNode);
// Update the relevant information after topology sorting
                    for(Node node : transformableNode.node.successorNodes){
                        TransformableNode successor = nodeMapTransformNode.get(node);
                        int temp = transformNodeMapPrecursorSize.get(successor);
transformNodeMapPrecursorSize.put(successor, temp - 1); // The successor node has not processed the successor number -1

                        transformableNode.successors.add(successor);
                        successor.precursors.add(transformableNode);
                    }
                    fl = 1;

// Is the general loop caused by the loop conditional branch? Find the conditional branch in the loop
                    if (cycleFlag & transformableNode.node.unit instanceof IfStmt) {
                        transformableNode.isCycle = true;
                        cycleFlag = false;
                    }

                    break;
                }
            }
// Because I have a layer of while(!waiting.isEmpty())
// So if a loop appears, transformNodeMapPrecursorSize.get(transformableNode) == 0 can't get over
// Then fl cannot be 1, so it enters the following ring-in processing
            if(fl == 0){
// Find the remaining nodes with the highest entry level: Reason: There are loops in the loop, and the most likely entry level is the loop entry level
                TransformableNode transformableNode = waiting.iterator().next();
                int maxIn = 0;
                for(TransformableNode t : waiting){
                    if(t.precursors.size() > maxIn){
                        maxIn = t.precursors.size();
                        transformableNode = t;
                    }
                }
                ret.add(transformableNode);
                waiting.remove(transformableNode);
                for(Node node : transformableNode.node.successorNodes){
                    TransformableNode successor = nodeMapTransformNode.get(node);
                    int temp = transformNodeMapPrecursorSize.get(successor);
                    transformNodeMapPrecursorSize.put(successor, temp - 1);

                    transformableNode.successors.add(successor);
                    successor.precursors.add(transformableNode);
                }
                topologicalOrderFail = 1;
                cycleFlag = true;
            }

        }
        if(topologicalOrderFail == 1) error_cannot_topological_order ++;
        return ret;
    }


}
