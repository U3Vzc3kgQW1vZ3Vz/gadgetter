package jdd.config;

import java.io.FileNotFoundException;
import java.io.IOException;

import static jdd.config.SootConfig.constructCG;

/**
 * 用于初始化整个项目的配置
 */
public class InitConfig {
    public static void initAllConfig() throws IOException {
        ConfigUtil.init();

        ConfigUtil.initContainer();
    }
}
