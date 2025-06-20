package jdd.gadgets.collection.iocd.unit;

import lombok.Getter;
import lombok.Setter;
import jdd.gadgets.collection.markers.DependenceType;

@Getter
@Setter
public class DependenceRecord {
// E.g. ARRAY_SIZE: The left is array, the right is size; Class_MethodName: The left is class, and the right is its method name
// ASSIGNED_REAL: The value and the assigned relationship between fields detected in writeObject
    public String methodName = "";
    public DependenceType type;
    public FieldRecord leftRecordF;
    public FieldRecord rightRecordF;
}
