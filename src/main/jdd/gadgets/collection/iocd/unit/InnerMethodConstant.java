package jdd.gadgets.collection.iocd.unit;

import jdd.util.Pair;

import java.util.HashSet;

public class InnerMethodConstant {
    public MethodRecord methodRecord;
    public HashSet<Pair<Object, ConstantRecord.constantType>> constants = new HashSet<>();
}
