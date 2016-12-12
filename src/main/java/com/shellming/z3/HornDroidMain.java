package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Function;
import com.google.security.zynamics.binnavi.API.disassembly.Module;
import com.google.security.zynamics.binnavi.API.reil.ReilFunction;
import com.google.security.zynamics.binnavi.API.reil.ReilInstruction;
import com.google.security.zynamics.binnavi.Database.Exceptions.*;
import com.google.security.zynamics.binnavi.disassembly.INaviModule;
import com.google.security.zynamics.binnavi.disassembly.types.Section;
import horndroid.options;
import z3.Z3Engine;

import java.util.List;
import java.util.Map;

/**
 * Created by ruluo1992 on 12/4/2016.
 */
public class HornDroidMain {
    private static options hornDroidOptions = new options();
    public static void main(String[] args) throws Exception {
        final Z3Engine z3engine = new Z3Engine(hornDroidOptions);
        Module test = BinnaviUtil.getModuleByName("libnative-lib.so");
        Map<String, Function> funcs = BinnaviUtil.getNativeFuncs(test);
        Function func = funcs.get("Java_com_shellming_jninew_MainActivity_stringFromJNI");
        if (func != null) {
            List<ReilInstruction> instructions = BinnaviUtil.getInstructions(func);
            for (ReilInstruction instruction : instructions) {
                
                System.out.println(instruction.toString() + " ; meta data:" + instruction.getMetaData());
            }
        }

    }
}
