package jdd.gadgets.collection.iocd.unit;

import java.util.LinkedList;

public class CollisionRecord {
    public int type;
public MethodRecord collisionMethodRecord; // Method of collision
    public MethodRecord firstHashCodeMtd;
    public MethodRecord secondHashCodeMtd;
    public LinkedList<FieldRecord> top = new LinkedList<>();
public LinkedList<FieldRecord> first = new LinkedList<>(); // Record fields related to hashCode [The first element, the order can be called (sequential inversion test is performed during mutation testing)]
public LinkedList<FieldRecord> second = new LinkedList<>(); // If there is an empty one, it is considered a constant
}
