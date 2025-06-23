package jdd.config;

import java.io.FileNotFoundException;
import java.io.IOException;

import static jdd.config.SootConfig.constructCG;

/**
 * Used to initialize the entire project configuration
 */
public class InitConfig {
    public static void initAllConfig() throws IOException {
        ConfigUtil.init();

        ConfigUtil.initContainer();
    }
}
