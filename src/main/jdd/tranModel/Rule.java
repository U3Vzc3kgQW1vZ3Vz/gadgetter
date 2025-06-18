package jdd.tranModel;

import jdd.dataflow.node.MethodDescriptor;

public interface Rule {
    void apply(Transformable transformable, MethodDescriptor methodDescriptor);
}
