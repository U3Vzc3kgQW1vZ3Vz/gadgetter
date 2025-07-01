package jdd.tranModel.Taint;

import soot.SootField;
import soot.Type;
import soot.Value;

import java.util.HashSet;
import java.util.LinkedList;

public class Taint{
public Value object; // Polluted object
public LinkedList<SootField> accessPath = new LinkedList<>(); // a.b -> b.c -> c.d a.b.c.d->[b,c,d]If accessPath.size is 0, the entire object is polluted
    public HashSet<Taint> aliases = new HashSet<>();

// Return null indicates mismatch, return empty list indicates). taint matching object itself.
// Used to find the taints that b will bring. The taints that b itself will bring are easy to find. You just need to compare the object.
    public LinkedList<SootField> match(Value object, SootField field){
        if(object.equals(this.object)){
            if(accessPath.isEmpty()) return new LinkedList<>();
if(accessPath.get(0).equals(field)){ // ToDo: get(0)?
                LinkedList<SootField> subList = new LinkedList<>();
                for(int ind = 1; ind < accessPath.size(); ind++) subList.add(accessPath.get(ind));
                return subList;
            }
        }
        return null;
    }

// Determine whether a taint is itself/ divides fields more detailedly
    public boolean match(Taint taint){
        if (taint.object != this.object) return false;
        if (taint.accessPath.size() < this.accessPath.size())
            return false;

// TODO: Why ++ind
        for (Integer ind = 0; ind <this.accessPath.size(); ++ind){
            if (!this.accessPath.get(ind).equals(taint.accessPath.get(ind)))
                return false;
        }

        return true;
    }

    public Taint(Value object, LinkedList<SootField> accessPath){
        this.object = object;
        this.accessPath = accessPath;
    }

    public Taint(Value object){
        this.object = object;
        this.accessPath = new LinkedList<>();
    }

    @Override
    public int hashCode() {
        if(this.object == null || this.accessPath == null) return 123;
        return this.object.hashCode() + this.accessPath.size() * 113;
    }

    @Override
    public boolean equals(Object obj) {
        if(! (obj instanceof Taint)) return false;
        Taint taint = (Taint) obj;
        if((taint.object == null && this.object == null) || (taint.object != null && taint.object.equals(this.object))){
            if(this.accessPath.size() == taint.accessPath.size()){
                for(int ind = 0; ind < this.accessPath.size(); ind++){
                    if(!this.accessPath.get(ind).equals(taint.accessPath.get(ind))) return false;
                }
                return true;
            }
        }
        return false;
    }

    public Type getType(){
        if (object == null)
            return null;
        if (accessPath.isEmpty())
            return object.getType();
        return accessPath.getLast().getType();
    }

    public static void addTaint(Taint taint, HashSet<Taint> set){
        if (taint != null)
            set.add(taint);
    }

    public static void addTaint(HashSet<Taint> taints, HashSet<Taint> set){
        for (Taint taint: taints) {
            if (taint != null)
                set.add(taint);
        }
    }


    @Override
    public String toString(){
        return " [" + object + "  " + accessPath + "] ";
    }
}
