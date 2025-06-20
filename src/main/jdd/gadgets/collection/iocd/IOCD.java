package jdd.gadgets.collection.iocd;

import jdd.gadgets.collection.iocd.unit.*;
import jdd.markers.SinkType;
import org.apache.commons.collections4.map.ListOrderedMap;
import jdd.util.Pair;

import java.util.*;
import java.util.concurrent.LinkedBlockingQueue;

public class IOCD {
    public int hashCode;
    public boolean hashCollisionFlag = false;
public String sinkType; // sink type
public String protocol; // Record protocol information
public boolean needSerialize; // Record whether all serialized interfaces are inherited in the gadget chain

// In order to improve splicing efficiency, record some constraint information related to reflect splicing
    public boolean publicEntry;
    public String entryType = "none";

public LinkedList<Pair<Integer, String>> gadgetCallStack; // gadget chains
public LinkedList<ClassRecord> gadgetClasses = new LinkedList<>(); // Record class hierarchy
public HashSet<ClassRecord> conClassNodes = new HashSet<>(); // class nodes deviate from the gadget chains path (not necessarily accurate and necessary, choose as needed)
// Corresponding Condition hashCode: Is it necessary? Condition
    public LinkedHashMap<Integer,Boolean> conditionsRecords = new LinkedHashMap<>();
public HashSet<DependenceRecord> dependenceRecords = new HashSet<>(); // Record dependencies
public CollisionRecord hashCollisionRecord; // Record hash collision information
public HashSet<UsedSiteRecord> usedFieldsRecords = new HashSet<>(); // fields usage information record
public HashSet<ConditionRecord> supplementConditions = new HashSet<>(); // All non-trunk conditions

public List<SinkRecord> sinkRecords = new ArrayList<>(); // Record the relevant fields used to construct attack payloads for injecting sinks

}
