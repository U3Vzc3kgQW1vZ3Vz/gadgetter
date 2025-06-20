package jdd.gadgets.collection.iocd.unit;

import lombok.Getter;
import lombok.Setter;
import jdd.util.Pair;

import java.util.*;

@Getter
@Setter
public class SinkRecord {

    public String sinkClassName;
    public MethodRecord sinkMethod;
    public String jimpleUnitInfo;
    public HashSet<Pair<Integer, FieldRecord>> sinkField = new HashSet<>();

    public FieldRecord sinkClassBelongToF;
    public FieldRecord sinkMethodNameF;
    public FieldRecord sinkMethodF;
public FieldRecord sinkProxyInvokeType; //Record which proxy is it. This value needs to be replaced when switching to call objects.
public String trigger = "NONE"; // NONE: No limit is identified/no limit; getter; setter
    public LinkedHashSet<FieldRecord> sinkFilePathF = new LinkedHashSet<>();
    public FieldRecord sinkFileContentF;
}
