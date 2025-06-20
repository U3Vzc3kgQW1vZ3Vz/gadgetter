package jdd.gadgets.collection.iocd.unit;

import jdd.util.Pair;

import java.util.HashSet;

/**
 * 记录程序执行过程中的潜在常量
 * 先提供更详细的记录信息；看情况是否直接不区分，全部放一起随机选取变异
 */
public class ConstantRecord {
    public static enum constantType{INT,STR};
    public ClassRecord classRecord;
// constants in fields
    public HashSet<Pair<Object, ConstantRecord.constantType>> fieldsConstants = new HashSet<>();
// Constants inside the method
    public HashSet<InnerMethodConstant> innerMethodConstants = new HashSet<>();
}
