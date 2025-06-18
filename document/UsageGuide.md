## How to use
1. `git clone https://github.com/fdu-sec/JDD.git`

- Set `src/java` and `src/jdd` as `Sources Root`

2. Adjust `config.properties` as needed.


3. run `runner/SearchGadgetChains.main`

## Configuration (config.properties) item description
- `inputPath`: test project path


- `outputDir`: output directory. E.g. IOCDs


- `outPutDirName`: Name of the folder where IOCDs are stored


- `prioritizedGadgetChainLimit`: Output N highest prioritized gadget chains


- `fragmentLenLimit`: Limit the depth of inter-procedural analysis during gadget fragment search. The maximum number of gadgets for each gadget fragment is `fragmentLenLimit+2`.


- `chainLimit`: The upper limit on the total number of gadgets in a complete gadget chain.
  The relationship between "gadget chain" and "gadget fragment" can be found in our JDD paper.


- `methodLimitNum`: Generate and summarize gadget fragment and start a new round of fragment searching if a dynamic method call overrides no more than methodLimitNum.


- `protocol`: currently supports jdk, hessian, json (e.g. jackson, ...).
  - `needSerializable`: please adjust them together with `protocol`.
    - jdk: needSerializable = true
    - hessian: needSerializable = false or true
    - json: needSerializable = false or true


- `sinkRules`:
  - available options: classLoad,invoke,jndi,exec,secondDes,custom,file (e.g., `sinkRules = invoke,jndi,exec`)
    - A version that facilitates custom additions and modifications may come online later
    - Some sinks (in custom) that have not been added/tested after refactoring

    Note that, `invoke, jndi, exec, classLoad` are the most commonly used. Of course, to detect more comprehensive chains, you can configure all the sinkRules.


## Test Example
The test applications are located in the `testExample` directory. You can change the test application by changing the `inputPath` in the configuration file.

test application example 1: `Groovy`
```
sun.reflect.'annotation'.AnnotationInvocationHandler: void readObject(java.io.ObjectInputStream)
Proxy Map: entrySet()
org.codehaus.groovy.runtime.ConversionHandler: java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])
org.codehaus.groovy.runtime.ConvertedClosure: java.lang.Object invokeCustom(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])
groovy.lang.Closure: java.lang.Object call(java.lang.Object[])
```
One of unknown gadget chain detected by JDD.
```
java.util.concurrent.ConcurrentHashMap: void readObject(java.io.ObjectInputStream)
groovy.lang.GString: int hashCode()
groovy.lang.GString: java.lang.String toString()
groovy.lang.GString: java.io.Writer writeTo(java.io.Writer)
groovy.lang.Closure: java.lang.Object call()
```
In this application, JDD detected gadget chains that do not require the dynamic proxy feature, which expands the range of protocols that can be attacked. The known gadget chain could only be used in protocols that support dynamic proxies (e.g. JDK, but could not be used in Hessian).


test application example 2: `Vaadin`
Known chain
```
javax.management.BadAttributeValueExpException: void readObject(java.io.ObjectInputStream)
com.vaadin.data.util.PropertysetItem: java.lang.String toString()
com.vaadin.data.util.NestedMethodProperty: java.lang.Object getValue()
java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])
```
One of unknown gadget chain detected by JDD.
```
java.util.concurrent.ConcurrentHashMap: void readObject(java.io.ObjectInputStream)
java.util.AbstractMap$SimpleEntry: boolean equals(java.lang.Object)
java.util.AbstractMap: boolean access$000(java.lang.Object,java.lang.Object)
java.util.AbstractMap: boolean eq(java.lang.Object,java.lang.Object)
com.sun.org.apache.xpath.internal.objects.XStringForFSB: boolean equals(java.lang.Object)
com.vaadin.data.util.AbstractProperty: java.lang.String toString()
com.vaadin.data.util.LegacyPropertyHelper: java.lang.String legacyPropertyToString(com.vaadin.data.Property)
com.vaadin.data.util.MethodProperty: java.lang.Object getValue()
java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])
```