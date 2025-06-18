# Common Issues and Update Log

### Where is the outputs of JDD?

- `IOCD`

  set `outPutIOCD = true` in `config.properties`.

  ```
  JDD's outputs are stored in the `<outputDir>/<outPutDirName>` directory, with each gadget chain corresponding to an `IOCD` stored in a separate `json` file. For example, (the IOCD of the exact gadget chain described by Ysoserial in `Vaadin`)

  Note that, do not mistakenly treat the intermediate results stored in `interInfos` as the final output of JDD.
  ```

  For example, one of the generated IOCD for a gadget chain in `vaadin`:

  <img width="300" alt="截屏2025-01-29 21 36 12" src="https://github.com/user-attachments/assets/97b11963-b9ca-44d3-8bdd-7d5261d02f63" />

- Just `gadget chain`

  set `outPutIOCD = false` in `config.properties`.

  Check the detected chains in `<outputDir>/<outPutDirName>/DetectedGadgetChains.txt`


### Sink Rule Configuration
Modify the sink rules in `config.properties`: e.g., `sinkRules = exec,invoke,jndi,classLoad`

- In the current default configuration of JDD, we have commented out some sinks with relatively low actual impact. For example, if you need to reproduce and test JDD’s detection of urldns1, you need to uncomment the two lines of code (L94–95) in `JNDICheckRule.checkRisky`.

### Configuration of Gadget Fragment and Gadget Chain Length in JDD Detection.

Please note that if you wish for JDD to detect longer gadget chains, you should adjust the `fragmentLenLimit` and `chainLimit` values in the `config.properties` file accordingly.
- The meanings of these two configuration options can be found in the [Usage Guide](Usage%20Guide.md).

For instance, if you aim to detect gadget chains of length 23 (such as the "Depth Tests" (20) from Table 4 in the "Gleipner" paper), you should set `fragmentLenLimit`=21 and `chainLimit`=23 in the `config.properties` file. (In this case, there is only one gadget fragment; although the test depth is 20, the total length of the chain is 23.)

**Note that the `fragmentLenLimit` and `chainLimit` configuration options were expanded following the feedback from the "Gleipner" paper (on February 2, 2025).
By appropriately configuring these options, JDD could fulfills the depth gadget chain category, as well as more Ysoserial replicas. We greatly appreciate the feedback from the Gleipner authors.**

### Evaluation correction of JDD
We have contacted the authors of Gleipner, retested, and corrected some discrepancies in the evaluation results of JDD. They are updating the paper.

### Important Update Log
###### February 2, 2025: Extended some useful configuration options for easier use, e.g., `fragmentLenLimit` and `chainLimit` in `config.properties`.