package jdd.config;

import java.cg.CG;
import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import soot.*;
import soot.options.Options;
import soot.util.Chain;
import java.util.TimeOutTask;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;

@Slf4j
public class SootConfig {
    public static List<String> ignoreInfo = getIgnoreInfo();
// Here we set the threshold for the unanalyzed class merging under the same package to 10, for example, a.b.c.D1-D11 will be merged into a.b.c
    public static int loadClassCounter = 0, maxPackageRecordTime = 10;
    public static HashMap<String, Integer> packageRecordTime = new HashMap<>();

    public static void setSoot(String inputClassPath) throws FileNotFoundException {

        G.reset();
        Scene.v().releaseCallGraph();
        Scene.v().releasePointsToAnalysis();
        Scene.v().releaseActiveHierarchy();
        Scene.v().releaseReachableMethods();
        Scene.v().releaseFastHierarchy();
        Scene.v().releaseSideEffectAnalysis();
        Scene.v().releaseClientAccessibilityOracle();
//remove odd Application Class
        SootConfig.removeAllAppClz();

        Options.v().set_src_prec(Options.src_prec_class);
        Options.v().set_process_dir(Collections.singletonList(((inputClassPath))));
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(true);
        Options.v().set_prepend_classpath(true);
        Options.v().set_keep_line_number(true);
        Options.v().set_output_format(Options.output_format_jimple);
//        Options.v().set_output_dir(RegularConfig.outputDir+"/JimpleOutput/framework1");
        Options.v().set_drop_bodies_after_load(false);
// Options.v().set_no_bodies_for_excluded(true);
        Options.v().setPhaseOption("cg", "all-reachable:true");
        Scene.v().setSootClassPath(Scene.v().getSootClassPath() + File.pathSeparator + RegularConfig.sootClassPath);
        Scene.v().loadDynamicClasses();
        loadTargetClass();
    }


    public static void constructCG(){
        List<SootMethod> tmpMethods = new ArrayList<>(FragmentsContainer.sources);
        BasicDataContainer.cg = new CG(tmpMethods);
    }

// Remove all implementation classes
    public static void removeAllAppClz() {
        log.info("清除当前所有的Application Class");
//Get Scene object
        Scene scene = Scene.v();
//Get all application classes
        Chain<SootClass> appClasses = scene.getApplicationClasses();
//Create a temporary list to store the application class to be deleted
        List<SootClass> toRemove = new ArrayList<>();
//Transfer all application classes and add them to the temporary list
        for (SootClass appClass : appClasses) {
            toRemove.add(appClass);
        }
//Transf the temporary list and remove each application class from the Scene object
        for (SootClass appClass : toRemove) {
            scene.removeClass(appClass);
        }
    }

// Add the classes to be analyzed one by one to soot
    public static void loadTargetClass(){
        HashSet hashSet = new HashSet();
        String[] jdkPaths = RegularConfig.sootClassPath.split(File.pathSeparator);
        List<String> paths = new ArrayList<>(Arrays.asList(jdkPaths));
        paths.add(RegularConfig.inputPath);
        for(String path : paths){
            for(String cl : SourceLocator.v().getClassesUnder(path)){
                if(checkIgnore(cl)){ continue; }
                try{
// The timeout threshold for limiting loading is 100 seconds
                    (new TimeOutTask(){
                        @Override
                        protected void task() {
                            SootClass theClass = Scene.v().loadClassAndSupport(cl);
                            if (!theClass.isPhantom()) {
// There is a situation where the number of classes is inconsistent here because there are duplicate objects
                                theClass.setApplicationClass();
                                hashSet.add(theClass);
                                if(loadClassCounter % 10000 == 0){
                                    log.info("Collected {} classes.", loadClassCounter);
                                }
                                loadClassCounter++;
                            }
                        }
                        @Override
                        protected void timeoutHandler(){
                            log.error("将类" + cl + "导入到soot过程中超时，跳过处理");
                        }
                    }).run(10);

                }catch (Exception e){
                    log.error("加载类" + cl + "过程中出错：" + e.getMessage());
                }
            }
        }
        log.info("共加载：" + hashSet.size() + "个类，App.Size" + Scene.v().getApplicationClasses().size());
    }

// Check whether the imported class is considered to be ignored
    public static boolean checkIgnore(String clazzName){

        for(String ignoreInfoTmp : ignoreInfo){
            if(ignoreInfoTmp.startsWith("#")){ continue; }
            if(clazzName.contains(ignoreInfoTmp)){ return true; }
        }
        return false;

    }

// Get ignore classes in the list specified by an external user
    private static List<String> getIgnoreInfo() {

        List<String> lines = new LinkedList<>();
        String ignoreListPath = RegularConfig.configPath + File.separator + "ignoreInfo";
        try{
            File ignoreFile = new File(ignoreListPath);
            lines = FileUtils.readLines(ignoreFile, StandardCharsets.UTF_8);
// Statistics the number of packets that appear, processes classes that exceed the threshold, and writes new content to the file
            String packageName;
            List<String> removePackageList = new ArrayList<>();
            for(String l : lines){
                if(l.startsWith("#") || l.equals("")) { continue; }
                packageName = getPackageName(l);
                updatePackageRecordTime(packageName);
            }
if(maxPackageRecordTime <= 0 ) { maxPackageRecordTime = 10; } // Avoid exceptions
            if (packageRecordTime == null)
                packageRecordTime = new HashMap<>();
            for(String key : packageRecordTime.keySet()){
                int currentTime = packageRecordTime.get(key);
                if(currentTime > maxPackageRecordTime){
                    removePackageList.add(key);
                    lines.removeIf(line -> line.contains(key));
                    lines.add(key);
                    log.info(key + "包下有超过" + maxPackageRecordTime + "个类无法处理，忽略整个包");
                }
            }
// Avoid java.util.ConcurrentModificationException
            for(String rmPackage : removePackageList){ packageRecordTime.remove(rmPackage); }
            FileUtils.writeLines(new File(ignoreListPath), lines, false);
// If you start with comment # or it is an empty string, delete it
            lines.removeIf(line -> line.startsWith("#") || line.equals(""));
        }catch (IOException e){
            log.error("Load ignoreInfo from " + ignoreListPath + " failed!");
            System.exit(0);
        }
        return lines;

    }

    public static List<String> getBlackList(){
        List<String> lines = new LinkedList<>();
        String blackListPath = RegularConfig.configPath + File.separator + "testBlackList";
// RegularConfig.blackListPath
        try{
            File blackListFile = new File(blackListPath);
            lines = FileUtils.readLines(blackListFile, StandardCharsets.UTF_8);
// Statistics the number of packets that appear, processes classes that exceed the threshold, and writes new content to the file
            String packageName;
            List<String> removePackageList = new ArrayList<>();
            for(String l : lines){
                if(l.startsWith("#") || l.equals("")) { continue; }
                packageName = getPackageName(l);
                updatePackageRecordTime(packageName);
            }
if(maxPackageRecordTime <= 0 ) { maxPackageRecordTime = 10; } // Avoid exceptions

            if (packageRecordTime == null)
                packageRecordTime = new HashMap<>();
            for(String key : packageRecordTime.keySet()){
                int currentTime = packageRecordTime.get(key);
                if(currentTime > maxPackageRecordTime){
                    removePackageList.add(key);
                    lines.removeIf(line -> line.contains(key));
                    lines.add(key);
                    log.info(key + "包下有超过" + maxPackageRecordTime + "个类无法处理，忽略整个包");
                }
            }
// Avoid java.util.ConcurrentModificationException
            for(String rmPackage : removePackageList){ packageRecordTime.remove(rmPackage); }
            FileUtils.writeLines(new File(blackListPath), lines, false);
// If you start with comment # or it is an empty string, delete it
            lines.removeIf(line -> line.startsWith("#") || line.equals(""));
        }catch (IOException e){
            log.error("Load ignoreInfo from " + blackListPath + " failed!");
            System.exit(0);
        }
        return lines;
    }

// Update the number of times the packages in packageRecordTime appears according to the actual situation
    public static void updatePackageRecordTime(String packageName){
        if(packageRecordTime == null) { packageRecordTime = new HashMap<>(); }
        if(packageRecordTime.containsKey(packageName)){
            int time = packageRecordTime.get(packageName);
            packageRecordTime.put(packageName, ++time);
        } else {
            packageRecordTime.put(packageName, 1);
        }
    }

// Tool class, give a complete class name separated by ., get its package name
    public static String getPackageName(String className){

        if(className.equals("") || className.startsWith("#")){
            throw new IllegalArgumentException("className非法，当前值为：" + className);
        }
        String[] classNameSplit = className.split("\\.");
        className = className.replace("." + classNameSplit[classNameSplit.length - 1], "");
        return className;
    }
}
