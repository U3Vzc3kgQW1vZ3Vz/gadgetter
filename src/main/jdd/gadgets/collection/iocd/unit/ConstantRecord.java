package jdd.gadgets.collection.iocd.unit;

import jdd.util.Pair;

import java.util.HashSet;
/// Record potential constants during program execution
/// Provide more detailed recording information first; see if the situation is not distinguished directly, and all of them are randomly selected for mutations.
public class ConstantRecord {
    public static enum constantType{INT,STR};
    public ClassRecord classRecord;
// constants in fields
    public HashSet<Pair<Object, ConstantRecord.constantType>> fieldsConstants = new HashSet<>();
// Constants inside the method
    public HashSet<InnerMethodConstant> innerMethodConstants = new HashSet<>();
}
