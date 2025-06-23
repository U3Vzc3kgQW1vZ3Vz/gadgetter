package jdd.tranModel.Rules;

import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.markers.Stage;
import jdd.tranModel.Rule;
import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

import java.util.HashSet;

public class JoinRule implements Rule {
    /**
     * It is generally used to handle the control flow convergence point and merge state.
     * 1. After detecting the sink point, whether you need to continue searching in depth in the current callstacks path;
     * 2. It is used to collect the conditional branch information before the statement when collecting information.
     * Recorded forward node information: subsequent lightweight path sensitivity in dynamic proxy module
     * It is not commonly used path sensitive, but after reaching a node, you can view the information of the pre-condition node to infer the conditions that must be met to perform to that node, and perform finer granular detection during splicing.
     *
     * @Param transformable
     */

    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {

        if (!BasicDataContainer.openJoinRule) return;
        TransformableNode tfNode = (TransformableNode) transformable;
// If there is no successor node, no analysis is required
        if (tfNode.precursors.isEmpty()
                || BasicDataContainer.stage.equals(Stage.OFF)
                || BasicDataContainer.stage.equals(Stage.FRAGMENT_LINKING))
            return;

        HashSet<Integer> path_record = new HashSet<>();
        for (TransformableNode precursor : tfNode.precursors) {
            if (!precursor.exec) {
                tfNode.exec = false;
            }

            path_record.addAll(precursor.path_record);
        }
        tfNode.path_record.addAll(path_record);

// if (BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING_SINGLE) && BasicDataContainer.openDynamicProxyDetect){
// recordPath(tfNode);
// }
    }

    public void recordPath(TransformableNode tfNode) {
        Stmt stmt = (Stmt) tfNode.node.unit;

        if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            Stmt target = ifStmt.getTarget();

// TransformableNode.ifStmtHashMap.put(ifStmt.hashCode(),transformableNode);
            BasicDataContainer.conditionTfNodesMap.put(ifStmt.hashCode(), tfNode);

            for (TransformableNode success : tfNode.successors) {
                if (((Stmt) success.node.unit).equals(target)) {
                    if (!tfNode.isCycle)
                        success.path_record.add(ifStmt.hashCode());
                } else {
                    success.path_record.add(-ifStmt.hashCode());
                }
            }
        }
    }
}
