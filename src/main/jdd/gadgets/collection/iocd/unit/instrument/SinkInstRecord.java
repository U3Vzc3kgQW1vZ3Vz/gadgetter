package jdd.gadgets.collection.iocd.unit.instrument;

import lombok.Getter;
import lombok.Setter;

import java.util.HashSet;

@Getter
@Setter
public class SinkInstRecord {
public MethodInstRecord methodInstRecord; // Record sink point method
public HashSet<Integer> pollutedParams = new HashSet<>(); // Parameters that should be contaminated are used to dynamically detect whether these parameters are contaminated.
    public boolean flag = true;
}
