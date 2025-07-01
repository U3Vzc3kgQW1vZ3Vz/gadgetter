package jdd.util;

import com.google.gson.Gson;
import jdd.config.RegularConfig;
import jdd.container.BasicDataContainer;
import jdd.container.RulesContainer;
import lombok.extern.slf4j.Slf4j;
import jdd.markers.SinkType;
import org.apache.commons.io.FileUtils;
import soot.SootMethod;
import jdd.structure.RuleDataStructure;
import jdd.structure.taint.TaintSpreadRuleUnit;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.LinkedList;

@Slf4j
public class DataSaveLoadUtil {
    /**
     * Tool class, used to serialize objects in Json
     * @param o
     * @return Json serialized data
     */
    public static String toGJson(Object o){
        Gson gson = new Gson();
        return gson.toJson(o);
    }

    public static Object toObject(String json, Class clazzType){
        Gson gson = new Gson();
        return gson.fromJson(json, clazzType);
    }

// Load ruleDataStructure
    public static void loadRuleDataStructure() throws IOException {
        String rulesPath = RegularConfig.configPath + File.separator + "RuleDataStructure.json";
        String jsonContent = FileUtils.readFileToString(new File(rulesPath),"utf-8");

        RulesContainer.ruleDataStructure = (RuleDataStructure) toObject(jsonContent, RuleDataStructure.class);
// Initialize Rules
        for (TaintSpreadRuleUnit taintSpreadRuleUnit: RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits()){
            taintSpreadRuleUnit.init();
            BasicDataContainer.blackList.addAll(taintSpreadRuleUnit.methodSigs);
        }
    }

// Store updated ruleDataStructure
    public static void saveRuleDataStructure(){
        if (RulesContainer.ruleDataStructure == null)
            return;

        String outPutJson = toGJson(RulesContainer.ruleDataStructure);
        String rulesPath = RegularConfig.configPath + File.separator + "RuleDataStructure.json";
        try{
            FileWriter out = new FileWriter(rulesPath, false);
            out.write(outPutJson);
            out.flush();
        } catch (IOException e){
log.error("Could not write result to " + rulesPath + "!");
            e.printStackTrace();
        }
    }

    public static void saveTaintSpreadRules(HashSet<TaintSpreadRuleUnit> candidateTaintSpreadRuleUnits){
        assert RulesContainer.ruleDataStructure != null;
        RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits().addAll(candidateTaintSpreadRuleUnits);
    }

    public static void saveTaintSpreadRule(TaintSpreadRuleUnit candidateTaintSpreadRuleUnit){
        assert RulesContainer.ruleDataStructure != null;
        RulesContainer.ruleDataStructure.getTaintSpreadRuleUnits().add(candidateTaintSpreadRuleUnit);
    }

    /**
     * Record call stack - sink type information into the output file
     * @param callStack
     * @param sinkType
     */
    public static void recordCallStackToFile(LinkedList<SootMethod> callStack, SinkType sinkType,
                                             String fileName, boolean printFlag) throws IOException {
        SootMethod entryMtd = callStack.get(0);
        FileWriter out = openOrCreateFileWriter(fileName, true);
// new FileWriter(fileName,true);
        try {
            String first = "["+sinkType+" Gadget] "+entryMtd.getSignature();
            out.write(first);
            out.write("\n");
            if (printFlag)
                System.out.println(first);

            for (int i=1; i<callStack.size();i++) {
                String info ;
                info = " -> "+callStack.get(i).getSignature();;
                out.write(info);
                out.write("\n");

                if (printFlag)
                    System.out.println(info);
            }
            out.write("\n");
            out.flush();
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        } finally {
            if (out != null)
                out.close();
        }
    }

    public static boolean fileExistOrNot(String filePath){
        File file = new File(filePath);
        return file.exists();
    }

    public static FileWriter openOrCreateFileWriter(String filePath, boolean appendFlag) throws IOException {
        Path directoryPath = Paths.get(filePath).getParent();
        try {
            if (Files.notExists(directoryPath)) {
                Files.createDirectories(directoryPath);
            }
        }catch (Exception e){e.printStackTrace();}

        if (fileExistOrNot(filePath))
            return new FileWriter(filePath,appendFlag);

        try {
            File file = new File(filePath);
            boolean fileCreated = file.createNewFile();
            if (fileCreated){
log.info("Created File: "+filePath);
}else log.info("Failed to create file: "+filePath);

            FileWriter fileWriter = new FileWriter(filePath, appendFlag);
            return fileWriter;
        }catch (Exception e){
            e.printStackTrace();
        }
        return null;
    }

    public static void createDir(String targetDir){
        Path targetPath = Paths.get(targetDir);
        if (!Files.exists(targetPath)){
            try {
                Files.createDirectories(targetPath);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
