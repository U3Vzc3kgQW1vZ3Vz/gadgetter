package jdd.gadgets.collection.rule;

import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.collection.node.ConditionNode;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.collection.node.GadgetNode;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

import java.io.IOException;

public class ConditionCheck implements InferRule{
    @Override
    public void apply(MethodDescriptor descriptor,
                      GadgetInfoRecord gadgetInfosRecord,
                      Transformable transformable) throws IOException {
        TransformableNode tfNode = (TransformableNode) transformable;
        IfStmt ifStmt = tfNode.getIfStmt();
        if (ifStmt == null)
            return;
        GadgetNode gadgetNode = gadgetInfosRecord.getGadgetNode(descriptor.sootMethod);
        if (gadgetNode == null) return;

        Stmt target = ifStmt.getTarget();
        BasicDataContainer.conditionTfNodesMap.put(ifStmt.hashCode(), tfNode);

        ConditionNode newConditionNode = new ConditionNode(tfNode, descriptor, false);
        gadgetInfosRecord.putConditionNode(newConditionNode, gadgetNode, ifStmt);

        for (TransformableNode success: tfNode.successors){
            if (((Stmt)success.node.unit).equals(target) ){
                if (!tfNode.isCycle)
                    success.path_record.add(ifStmt.hashCode());
            }else {
                success.path_record.add(-ifStmt.hashCode());
            }
        }
    }
}
