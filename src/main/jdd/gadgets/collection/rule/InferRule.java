package jdd.gadgets.collection.rule;

import jdd.tranModel.Transformable;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.collection.node.GadgetInfoRecord;

import java.io.IOException;

public interface InferRule {
    void apply(MethodDescriptor descriptor,
               GadgetInfoRecord gadgetInfosRecord,
               Transformable transformable) throws IOException;
}
