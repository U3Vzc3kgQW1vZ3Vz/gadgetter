package jdd.config;

import jdd.container.BasicDataContainer;
import jdd.container.FieldsContainer;
import jdd.container.FragmentsContainer;
import jdd.container.RulesContainer;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.io.FileUtils;
import jdd.util.Utils;

import java.io.*;
import java.util.*;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

@Slf4j
public class ConfigUtil {

    public static Properties configProperties = new Properties();
// List of folders that are not processed during the decompression process
    private static String[] unDecompressDirList = { "META-INF", "OSGI-INF" };
    private static String[] specialDirList = { "/lib/", "WEB-INF/classes/" };
    private static HashSet<String> runtimeSpecialDirList = new HashSet<>();
    private static int classNums = 0;

// Used for initialization work, including directory creation, configuration item loading and Soot initialization
    public static void init() throws FileNotFoundException {

        try{
// Load the configuration file and read the parameters
            initConfig();
            SootConfig.setSoot(RegularConfig.inputPath);
        }catch (FileNotFoundException e){
log.error("File Not Found: " + e.getMessage());
            e.printStackTrace();
        }catch (IOException e){
            e.printStackTrace();
        }

    }

    public static void initContainer() throws IOException {
        BasicDataContainer.init();
        RulesContainer.init();
        FragmentsContainer.init();
        FieldsContainer.init();
    }

    /**
     * Given the File handle that encapsulates the folder dir, delete all empty folders under the folder.
     * @param dirFile
     */
    public static void deleteEmptyUnderDir(File dirFile) throws IOException {

        if(!dirFile.isDirectory()){ throw new IllegalArgumentException("Parameter dirFile should be DIRECTORY!"); }
        File[] filesUnderDir = dirFile.listFiles();
// If the length is zero, it will be deleted directly, because it has been confirmed that it is a folder File
// Therefore, there will be no null
        if(filesUnderDir.length == 0){ return; }
// If the length is not zero, then recursively process it
        for(File file : filesUnderDir){
            if(file.isDirectory()){ deleteEmptyUnderDir(file); }
        }
// After recursively returning, determine the files in the current directory again
        if(FileUtils.isEmptyDirectory(dirFile)){ FileUtils.deleteDirectory(dirFile);}

    }

    public static List<File> getAllJarFiles(String dir){

        List<File> files = new ArrayList<>();
        File dirFile = new File(dir);
        if(!dirFile.isDirectory()){
            throw new IllegalArgumentException(dir + " is not a directory!");
        }

        File[] tmpFiles = dirFile.listFiles();
        List<File> jarFiles = new ArrayList<>();
        List<File> dirFiles = new ArrayList<>();
// Get the jar file in the current directory
        for(File file : tmpFiles){
// For temporary storage of the directory
            if(file.isDirectory()){
                dirFiles.add(file);
                continue;
            }
            String fileName = file.getName();
            if(!fileName.endsWith("jar") && !fileName.endsWith(".war")){ continue; }
            jarFiles.add(file);
        }
        files.addAll(jarFiles);
// Get the jar file in the subdirectory in the current directory
        for(File dFile : dirFiles){
            List<File> tmpJarFiles = getAllJarFiles(dFile.getAbsolutePath());
            files.addAll(tmpJarFiles);
        }
        return files;
    }


    /**
     * Unzip all jar packages in directory dir to outPutDir/tmp/ directory
     * @param dir format is /path/to/lib/dir/
     */
    public static void decompressJarFromDir(String dir) throws IOException {

// Unzip all jar files of dir into the dir/tmp/ directory
        try{
// Create a temporary folder
            String tmpDir = "tmp/";
            File tmpDirFile = new File(dir + tmpDir);
            if(tmpDirFile.exists()){
log.info("There is a legacy historical tmp folder, use the tmp folder as the class path for analysis input. If there is a new project to analyze, please delete the folder");
                return;
            }
            tmpDirFile.mkdirs();
// Get all Jar files in the directory
            List<File> jarFiles = getAllJarFiles(dir);
            for(File jarFile : jarFiles){
// Decompression
                JarFile jar = new JarFile(jarFile);
                decompressJar(jar, dir + tmpDir);
            }
log.info("Co-decompression" + classNums + "classes");
// Process some special directories, such as WEB-INF/classes, move them to the tmp directory, so that the class path of the class in this folder is correct
            for(String specialDir : runtimeSpecialDirList){
                File srcDir = new File(specialDir);
                if(FileUtils.isDirectory(srcDir)){
                    File[] filesUnderSpecialDir = srcDir.listFiles();
                    for(File file : filesUnderSpecialDir){
                        String name = file.getName();
                        if(file.isDirectory()){
                            FileUtils.copyDirectoryToDirectory(file, new File(dir + tmpDir));
                            FileUtils.deleteDirectory(file);
                        }else{
                            FileUtils.copyFile(file, new File(dir  + tmpDir + name));
                            FileUtils.delete(file);
                        }
                    }
                }
            }
// Delete the unzipped empty folder
            deleteEmptyUnderDir(tmpDirFile);
        }catch (IOException e){
            e.printStackTrace();
        }
    }

    /**
     * Functional functions for decompressing a single jar package
     * @param jarFile Jar package encapsulated by JarFile objects
     * @param outputDir decompressed directory
     */
    public static void decompressJar(JarFile jarFile, String outputDir) throws IOException {

        if(jarFile == null || outputDir == null) {
            throw new IllegalArgumentException("Method parameters should not be null!");
        }
        if(outputDir.equals("")) {
            throw new IllegalArgumentException("Parameter outputDir should not be empty!");
        }

// Get each file in jarFile and extract it to outputDir
        Enumeration<JarEntry> entries = jarFile.entries();
        List<String> newJarWarPaths = new ArrayList<>();
        while(entries.hasMoreElements()){

            JarEntry entry = entries.nextElement();
            String entryName = entry.getName();
            String path = outputDir + entryName;
            File newFile = new File(path);
// Does not process the contents under the { META-INF, OSGI-INF } folder
            boolean flag = false;
            for (String ignoreDirName : unDecompressDirList) {
                if(entryName.contains(ignoreDirName)){
                    flag = true;
                    break;
                }
            }
            if(flag){ continue; }
// If it is some special folder containing the class, then record it
            for(String specialDir : specialDirList){
                if(path.endsWith(specialDir)){
                    runtimeSpecialDirList.add(path);
                }
            }
// If this entry is a folder and does not exist, then create it
            if(entry.isDirectory()){
                if(!newFile.exists()) { newFile.mkdirs(); }
                continue;
            }
// If it is a file, then determine whether the folder it is in is there. Then decompression
// If it is a jar/war file, then decompress it on the spot and record it waiting for the next round of processing.
            boolean isJar = false;
            if(entryName.endsWith(".jar") || entryName.endsWith(".war")){
                isJar = true;
                String[] splitedEntryName = entryName.split("/");
                String jarWarFileName = splitedEntryName[splitedEntryName.length - 1];
                path = outputDir + jarWarFileName;
                newJarWarPaths.add(path);
                newFile = new File(path);
            }
// If it is not a class file, then there is no need to unzip it
            if(!entryName.endsWith(".class") && !isJar ) { continue; }
            File newFileParent = newFile.getParentFile();
            if(!newFileParent.exists()) { newFileParent.mkdirs(); }
            InputStream inputStream = jarFile.getInputStream(entry);
            OutputStream outputStream = new BufferedOutputStream(new FileOutputStream(newFile));
// Decompression processing
            byte[] buffer = new byte[2048];
            int bytesNum = 0;
            while((bytesNum = inputStream.read(buffer)) > 0){ outputStream.write(buffer, 0, bytesNum); }
            outputStream.flush();
            outputStream.close();
            inputStream.close();
            classNums++;
        }
// Handle the newly unzipped jar in the current fat jar
        for(String newJarWarPath : newJarWarPaths){
            JarFile newJarFile = new JarFile(newJarWarPath);
            decompressJar(newJarFile, outputDir);
// Delete these intermediate jar packages
            FileUtils.delete(new File(newJarWarPath));
        }
    }



// Determine whether it is a Unix-like system
    public static  boolean isOnServer(){
        return !System.getProperty("os.name").contains("Windows") & !System.getProperty("os.name").contains("Mac OS X");
    }
    private static String getWorkDir(){ return System.getProperty("user.dir") + "/"; }
// Determine whether it is an absolute path
    private static boolean isAbsolute(String path){
        if(isOnServer()){ return path.startsWith("/"); }
        return path.indexOf(":") > 0 | path.startsWith("/");
    }

    public static void initConfig() throws IOException {
// Load configuration items and set jdk dependency type
        ConfigUtil.loadConfig("config/config.properties");
        RegularConfig.sootClassPath = ConfigUtil.getJdkDependencies(RegularConfig.withAllJdk);

log.info("[ detect project :" + RegularConfig.inputPath + " ]");
// Unzip all jar/war packages under inputClassPath
log.info("Decompress directory" + RegularConfig.inputPath + "class information");
        ConfigUtil.decompressJarFromDir(RegularConfig.inputPath);
        RegularConfig.inputPath = RegularConfig.inputPath + "tmp/";
log.info("Decompression is completed");
    }

    private static String getPathProperty(String pathKey){

// Get the running directory of the current program
        String workDir = getWorkDir();
// The judgment is to configure the path
        String tmpValue = configProperties.getProperty(pathKey);
        if(Objects.equals(tmpValue, "") || Objects.equals(tmpValue, null)) {
            throw new IllegalArgumentException("Config property " + pathKey + " not found");
        }
        return isAbsolute(tmpValue) ?
                tmpValue :
                workDir + tmpValue;
    }

    /**
     * Used to obtain the jdk dependencies on the running program machine. We only use { lib/jce.jar, lib/rt.jar, lib/ext/nashron.jar } by default.
     * @param withAllJdk
     * @return jdkDependencies, is a String. That is, the dependency classpath separated by File.pathSeparator
     */
    public static String getJdkDependencies(String withAllJdk){
        String javaHome = System.getProperty("java.home");
//        String javaHome = "/Library/Java/JavaVirtualMachines/jdk1.7.0_21.jdk/Contents/Home/jre";
        String[] jre;

        if("true".equals(withAllJdk)){
            jre = new String[]{"../lib/dt.jar","../lib/sa-jdi.jar","../lib/tools.jar",
                    "../lib/jconsole.jar","lib/resources.jar","lib/rt.jar","lib/jsse.jar",
                    "lib/jce.jar","lib/charsets.jar","lib/ext/cldrdata.jar","lib/ext/dnsns.jar",
                    "lib/ext/jaccess.jar","lib/ext/localedata.jar","lib/ext/nashorn.jar",
                    "lib/ext/sunec.jar","lib/ext/sunjce_provider.jar","lib/ext/sunpkcs11.jar",
                    "lib/ext/zipfs.jar","lib/management-agent.jar"};
        }else{
            jre = new String[]{"lib/rt.jar","lib/jce.jar", "lib/ext/nashron.jar"};
        }

        StringBuilder tmpJdkDependencies = new StringBuilder();
        for(String cp:jre){
            String path = String.join(File.separator, javaHome, cp);
            File file = new File(path);
            if(file.exists()){
                tmpJdkDependencies.append(path);
                tmpJdkDependencies.append(File.pathSeparator);
            }
        }
        tmpJdkDependencies.deleteCharAt(tmpJdkDependencies.length()-1);

        return tmpJdkDependencies.toString();
    }


    /**
     * Used to obtain configuration items from a specific file path, default is config/config.properties
     * @param filePath
     */
    public static void loadConfig(String filePath){
        try{

            if (isOnServer()){

                //TODO: fix later tonight

                filePath = System.getProperty("user.dir")+File.separator+"config/config.properties";
            }
log.info("filePath = "+filePath);
            Reader configReader = new FileReader(filePath);
            configProperties.load(configReader);

// Load configuration items
            RegularConfig.outputDir = getPathProperty(ConfigurationEnum.OUTPUT_DIR.toString());
            RegularConfig.inputPath = getPathProperty(ConfigurationEnum.INPUT_PATH.toString());
            RegularConfig.configPath = getPathProperty(ConfigurationEnum.CONFIG_PATH.toString());
            RegularConfig.outPutDirName = configProperties.getProperty(ConfigurationEnum.OUT_PUT_DIR_NAME.toString(), "infos");
            RegularConfig.accessPath_limit =
                    Integer.parseInt(configProperties.getProperty(ConfigurationEnum.ACCESS_PATH_LIMIT.toString(), "3"));
            RegularConfig.withAllJdk =
                    configProperties.getProperty(ConfigurationEnum.WITH_ALL_JDK.toString(), "false");
            RegularConfig.intermediary_quantity =
                    Integer.parseInt(configProperties.getProperty(ConfigurationEnum.INTERMEDIARY_QUANTITY.toString(),"2"));
            RegularConfig.protocol = configProperties.getProperty(ConfigurationEnum.PROTOCOL.toString(), "jdk");
            BasicDataContainer.methodLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.METHOD_LIMIT_NUM.toString(), "5"));
            RegularConfig.jsonSourceTypes = (HashSet<String>) Utils.toSet(configProperties.getProperty(ConfigurationEnum.JSON_SOURCE_TYPE.toString(), "getter"));
            RegularConfig.storeInDataBase =
                    configProperties.getProperty(ConfigurationEnum.STORE_IN_DATABASE.toString(), "true");
            RegularConfig.prioritizedGadgetChainLimit = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.PRIORITIZED_GADGET_CHAIN_LIMIT.toString(), "-1"));
            RegularConfig.inputEXPInfosPath = getPathProperty(ConfigurationEnum.INPUT_EXP_PATH.toString());
            BasicDataContainer.chainLimit = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.CHAIN_LIMIT.toString(), "20"));
            BasicDataContainer.stackLenLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.FRAGMENT_LEN_LIMIT.toString(), "6"));
            RegularConfig.needSerializable = configProperties.getProperty(ConfigurationEnum.NEED_SERIALIZABLE.toString(), "true").equals("true");
            BasicDataContainer.needSerializable = RegularConfig.needSerializable;
            RegularConfig.outPutIOCD = configProperties.getProperty(ConfigurationEnum.OUTPUT_IOCD.toString(), "true").equals("true");
            RegularConfig.linkMode = configProperties.getProperty(ConfigurationEnum.LINK_MODE.toString(), "strict").equals("strict")? "strict":"loose";
            RegularConfig.derivationType = configProperties.getProperty(ConfigurationEnum.DERIVATION_TYPE.toString(),"all");
            RegularConfig.taintRuleMode = configProperties.getProperty(ConfigurationEnum.TAINT_RULE_MODE.toString(), "strict");
            RegularConfig.sinkRules = (HashSet<String>) Utils.toSet(configProperties.getProperty(ConfigurationEnum.SINK_RULES.toString()));
            BasicDataContainer.openDynamicProxyDetect = configProperties.getProperty(ConfigurationEnum.OPEN_DYNAMIC_PROXY.toString(), "false").equals("true");
            RegularConfig.executionTimeLimit = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.EXECUTION_TIME_LIMIT.toString(), "60"));
            RegularConfig.reRunLimitNum = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.RE_RUN_LIMIT_NUM.toString(), "1"));
            BasicDataContainer.heuristicShortChainCutLen = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.Heuristic_Short_Chain_Cut_Len.toString(), "0"));
            BasicDataContainer.serializableInterceptLen = Integer.parseInt(configProperties.getProperty(ConfigurationEnum.SERIALIZABLE_INTERCEPTLEN.toString(), "2"));

        }catch (IOException e){
            throw new IllegalArgumentException("config file not found!");
        }
    }
}
