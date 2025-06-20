package jdd.gadgets.collection.iocd.unit;

import java.util.HashMap;
import java.util.HashSet;

public class UsedSiteRecord {
public String inClassName; // Which class file is used
public Integer site; // Where is it

    public HashSet<FieldRecord> usedFields = new HashSet<>();
}
