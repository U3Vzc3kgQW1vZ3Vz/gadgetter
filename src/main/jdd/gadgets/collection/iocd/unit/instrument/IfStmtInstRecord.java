package jdd.gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;

@Setter
@Getter
public class IfStmtInstRecord {
public String className; // The class name to which the condition branch belongs
public String methodSubSig; // The sub signature of the method to which this condition branch belongs
    public String methodName;
public Integer lineNumber; // Location in the source code file
public boolean basic = false; // Is it Basic Condition
public Integer hashCode; // Used to mark which ConditionRecord
public HashSet<Integer> successor; // successor of this condition branch
public Integer basicSuccessor; // If it is Basic Condition, the subsequent successor statement locations that should be entered will be recorded.
// public HashSet<Integer> precursor; // The precursor of this condition branch

}
