package jdd.gadgets.collection.iocd.unit;

import jdd.dataflow.node.SourceNode;
import jdd.util.Pair;
import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

@Getter
@Setter
public class ClassRecord {

public String className; // Current class
public int id; // Identify class Node, which is convenient for processing when multiple instances of the same type appear.
// Record <Previous Class - Properties under Previous Class>, if null, the first class
// public Pair<String, String> predecessorRecord;
// public LinkedList<String> preAccessPath = new LinkedList<>();
    public SourceRecord sourceRecord;
    public HashSet<SourceRecord> candidateSources = new HashSet<>();
// // From MethodRecord -> LinkedList<MethodRecord>, because it may happen to call back to the class from other functions
// public LinkedList<MethodRecord> predecessorMethods = new LinkedList<>();
    public MethodRecord predecessorMethod;
// field - <Which class file is used, the number of lines in the class file>
    public HashSet<FieldRecord> usedFields;
    public List<FieldRecord> fields;
public List<FieldRecord> conFields; // fieldRecord record
    public LinkedList<ConditionRecord> allConditions;
    public LinkedList<MethodRecord> usedMethods;
    public boolean isProxy;
    public String triggerMethod;
public HashSet<String> addProxyInterface = new HashSet<>(); // The class interface inherited when encapsulated as dynamic proxy instance (TODO: temporarily removed, and then reintegrate after the test is stable)
    public boolean flag = true;
    public boolean changed = true;
}
