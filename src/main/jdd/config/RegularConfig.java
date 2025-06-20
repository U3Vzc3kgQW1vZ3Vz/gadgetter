package jdd.config;


import java.util.HashSet;
import java.util.Set;

public class RegularConfig {

// Configuration file specification
    public static String inputPath;
    public static String outPutDirName;
    public static String outputDir;
    public static String withAllJdk;
    public static String configPath;
    public static int accessPath_limit;
    public static int executionTimeLimit = 60;
    public static int reRunLimitNum = 1;
// Agreement selection
    public static String protocol;
    public static String linkMode;
    public static boolean outPutIOCD;
// Whether to deposit mysql
    public static String storeInDataBase;

    public static int intermediary_quantity;

    public static String sootClassPath;
    public static String inputEXPInfosPath;
    public static boolean needSerializable;
    public static String taintRuleMode;
    public static Integer prioritizedGadgetChainLimit;
    public static String derivationType;
    public static HashSet<String> sinkRules = new HashSet<>();
    public static HashSet<String> jsonSourceTypes;
}
