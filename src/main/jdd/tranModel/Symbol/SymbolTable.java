package jdd.tranModel.Symbol;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class SymbolTable {
    public HashMap<String, SymbolRecord> nameMapSymbolRecords = new HashMap<>();

    public SymbolRecord get(String name){
        if(!nameMapSymbolRecords.containsKey(name)) return null;
        return nameMapSymbolRecords.get(name);
    }

    public boolean containsName(String name){
        return nameMapSymbolRecords.containsKey(name);
    }

    public void addEntry(String name, String infoEntry){
        if(!containsName(name)) nameMapSymbolRecords.put(name, new SymbolRecord(name));
        SymbolRecord symbolRecord = get(name);
        symbolRecord.addEntry(infoEntry);
    }

    public List<String> getInfo(String name){
        SymbolRecord symbolRecord = get(name);
        if(symbolRecord == null) return new LinkedList<>();
// hack: Return the object itself directly, we trust the caller
        return symbolRecord.info;
    }

    public boolean containsEntry(String name, String infoEntry){
        if(!containsName(name)) return false;
        return get(name).containsEntry(infoEntry);
    }
}
