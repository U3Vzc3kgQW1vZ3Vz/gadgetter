package jdd.gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashMap;
import java.util.HashSet;

@Getter
@Setter
public class Instruments {
// Class name <-> Existing IfStmt
    public HashMap<String, HashSet<IfStmtInstRecord>> classIfStmtsMap = new HashMap<>();

// // call site record
// public HashMap<String, HashSet<CallSiteInstRecord>> classCallsitesMap = new HashMap<>();

// How to enter the stake
    public HashMap<String, HashSet<MethodInstRecord>> classMethodsMap = new HashMap<>();
// Sink points to determine whether gadget is available
    public HashSet<SinkInstRecord> sinkRecords = new HashSet<>();
}
