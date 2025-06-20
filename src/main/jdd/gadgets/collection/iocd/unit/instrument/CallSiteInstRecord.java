package jdd.gadgets.collection.iocd.unit.instrument;

public class CallSiteInstRecord {
// Method information for calling this method
    public String callerClassName;
    public String callerSubSig;
    public String callerName;

// call site point information
    public String calleeClassName;
    public String calleeSubSig;
    public String calleeName;
    public boolean isAbstractOrInterface;
// Location
    public int lineNumber;
}
