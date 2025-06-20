package jdd.gadgets.collection.iocd.unit;
import jdd.util.Pair;
import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;

@Setter
@Getter
public class FieldRecord{

public String classBelongTo; //What kind of field is it?
public int classId; // The corresponding Class Node id
    public String fieldName;
public String fieldType; // Actual assignment type/field definition type
    public String sig;
// When used to deal with a.b(), a cannot be null.
    public boolean isNotNull;
public boolean isTransient; // Is it a field of type transient

public HashSet<FieldRecord> fields = new HashSet<>(); // field.field

    public int hashCode(){
        int hashCode = classBelongTo.hashCode()^13 + fieldName.hashCode()^7 + fieldType.hashCode();
        hashCode = hashCode^(fields.size());
        return hashCode;
    }

    public boolean equals(Object object){
        if (!(object instanceof FieldRecord))
            return false;

        FieldRecord fieldRecord = (FieldRecord) object;
        if (!classBelongTo.equals(fieldRecord.classBelongTo)
                | !fieldName.equals(fieldRecord.fieldName)
                | !sig.equals(fieldRecord.sig)
                | !fieldType.equals(fieldRecord.fieldType))
            return false;

        if (fields.size() != fieldRecord.fields.size())
            return false;

        return true;
    }

    public static boolean equals(FieldRecord fieldRecord1, FieldRecord fieldRecord2){
        if (!fieldRecord1.classBelongTo.equals(fieldRecord2.classBelongTo)
                | !fieldRecord1.fieldName.equals(fieldRecord2.fieldName)
                | !fieldRecord1.sig.equals(fieldRecord2.sig)
                | !fieldRecord1.fieldType.equals(fieldRecord2.fieldType))
            return false;

        return true;
    }
}
