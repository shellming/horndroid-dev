package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Function;
import com.google.security.zynamics.binnavi.API.disassembly.Module;
import com.google.security.zynamics.binnavi.API.reil.ReilBlock;
import com.google.security.zynamics.binnavi.API.reil.ReilFunction;
import com.google.security.zynamics.binnavi.API.reil.ReilInstruction;
import com.google.security.zynamics.binnavi.Database.Exceptions.*;
import com.google.security.zynamics.binnavi.disassembly.INaviFunction;
import com.google.security.zynamics.binnavi.disassembly.INaviModule;
import com.google.security.zynamics.binnavi.disassembly.types.Section;
import com.microsoft.z3.*;
import horndroid.options;
import z3.Z3Engine;
import z3.Z3Query;

import java.lang.reflect.Field;
import java.util.HashMap;
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
        Map<Long, String> addr2fun = new HashMap<>();
        Map<String, RFunction> name2fun = new HashMap<>();
        for (String funName : funcs.keySet()) {
            addr2fun.put(funcs.get(funName).getAddress().toLong(), funName);
            RFunction rFunction = new RFunction(funcs.get(funName));
            name2fun.put(funName, rFunction);
        }
        Function func = funcs.get("Java_com_shellming_jninew_MainActivity_stringFromJNI");
        INaviFunction naviFunc = func.getNative();
        ReilVariable variable = new ReilVariable(z3engine.getContext(), 64);
        ReilEngine reilEngine = new ReilEngine(z3engine.getContext(), 64, z3engine, variable);
        if (func != null) {
            List<ReilBlock> blocks = BinnaviUtil.getBlocks(func);
            RFunction rFunction = new RFunction(func);
            for (int b = 0; b < blocks.size(); b++) {
                List<ReilInstruction> instructions = blocks.get(b).getInstructions();
                for (int i = 0; i < instructions.size(); i++) {
                    System.out.println("process instruction:" + instructions.get(i).toString());
                    ReilInstruction instruction = instructions.get(i);
                    Long nextCode = 0L;
                    if (i != instructions.size() - 1) {
                        nextCode = instructions.get(i + 1).getAddress().__long__();
                    }
                    boolean isReturn = false;
                    if (blocks.get(b).getChildren().size() == 0) {
                        isReturn = true;
                    }
                    ReilInstructionAnalysis analysis =
                            new ReilInstructionAnalysis(instruction, rFunction, reilEngine, nextCode, addr2fun, name2fun, isReturn);
                    analysis.createHornClauses();
                }
            }
            System.out.println("done.");
            Context mContext = z3engine.getContext();
            Z3Query query = new Z3Query(mContext.mkFalse(), "", true, "", "", "", "");
            z3engine.addQuery(query);
            final Fixedpoint temp = mContext.mkFixedpoint();
            Class z3Class = z3engine.getClass();
            Field mRulesField = z3Class.getDeclaredField("mRules");
            mRulesField.setAccessible(true);
            List<BoolExpr> mRules = (List<BoolExpr>) mRulesField.get(z3engine);
            for(BoolExpr rule : mRules){
                temp.addRule(rule, null);
            }
            Field mFuncsField = z3Class.getDeclaredField("mFuncs");
            mFuncsField.setAccessible(true);
            List<FuncDecl> mFuncs = (List<FuncDecl>) mFuncsField.get(z3engine);
            for(FuncDecl fun : mFuncs){
                temp.registerRelation(fun);
                Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
                        mContext.mkSymbol("bound_relation")};
                temp.setPredicateRepresentation(fun, symbols);
            }
            z3engine.executeAllQueries();
            System.out.println(temp.toString());
        }

    }
}
