package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.*;
import com.google.security.zynamics.binnavi.API.reil.InternalTranslationException;
import com.google.security.zynamics.binnavi.API.reil.ReilBlock;
import com.google.security.zynamics.binnavi.API.reil.ReilFunction;
import com.google.security.zynamics.binnavi.API.reil.ReilInstruction;
import com.google.security.zynamics.binnavi.Database.CDatabase;
import com.google.security.zynamics.binnavi.Database.CDatabaseManager;
import com.google.security.zynamics.binnavi.Database.Exceptions.*;
import com.google.security.zynamics.binnavi.Database.Exceptions.CouldntConnectException;
import com.google.security.zynamics.binnavi.Database.Exceptions.CouldntInitializeDatabaseException;
import com.google.security.zynamics.binnavi.Database.Exceptions.CouldntLoadDataException;
import com.google.security.zynamics.binnavi.Database.Exceptions.CouldntLoadDriverException;
import com.google.security.zynamics.binnavi.Database.Exceptions.InvalidDatabaseException;
import com.google.security.zynamics.binnavi.Database.Exceptions.InvalidDatabaseVersionException;
import com.google.security.zynamics.binnavi.config.ConfigManager;
import com.google.security.zynamics.binnavi.config.DatabaseConfigItem;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by ruluo1992 on 12/4/2016.
 */
public class BinnaviUtil {
    private static CDatabase db;
    static {
        final CDatabaseManager manager = CDatabaseManager.instance();
        List<DatabaseConfigItem> dbs = ConfigManager.instance().getDatabases();
        DatabaseConfigItem database = new DatabaseConfigItem();
        database.setDescription("test");
        database.setDriver("org.postgresql.Driver");
        database.setHost("127.0.0.1:5432");
        database.setName("new_database");
        database.setUser("postgres");
        database.setPassword("casjldfgh1992");
        database.setIdentity("identity");
        database.setAutoConnect(false);
        database.setSavePassword(false);
        db = new CDatabase(database.getDescription(), database.getDriver(),
                database.getHost(), database.getName(), database.getUser(), database.getPassword(),
                database.getIdentity(), database.isSavePassword(), database.isAutoConnect());
        manager.addDatabase(db);
        DatabaseManager dbManager = new DatabaseManager(manager);
    }

    public static List<Module> getModules() throws LoadCancelledException, InvalidExporterDatabaseFormatException, CouldntInitializeDatabaseException, InvalidDatabaseException, CouldntLoadDriverException, CouldntConnectException, CouldntLoadDataException, InvalidDatabaseVersionException {
        db.connect();
        db.load();
        Database apiDatabase = new Database(db);
        List<Module> modules = apiDatabase.getModules();
        return modules;
    }

    public static Module getModuleByName(String name) throws LoadCancelledException, InvalidExporterDatabaseFormatException, CouldntLoadDataException, CouldntInitializeDatabaseException, InvalidDatabaseVersionException, InvalidDatabaseException, CouldntLoadDriverException, CouldntConnectException {
        List<Module> modules = getModules();
        for (Module module : modules) {
            if (module.getName().equals(name)) {
                return module;
            }
        }
        return null;
    }

    public static Map<String,Function> getNativeFuncs(Module module) throws com.google.security.zynamics.binnavi.API.disassembly.CouldntLoadDataException, InternalTranslationException {
        module.load();
        List<Function> functions = module.getFunctions();
        Map<String, Function> funcs = new HashMap<String, Function>();
        for (Function f : functions) {
            funcs.put(f.getName(), f);
        }
        return funcs;
    }

//    public static Map<String,ReilFunction> getReilFuncs(Module module) throws com.google.security.zynamics.binnavi.API.disassembly.CouldntLoadDataException, InternalTranslationException {
//        module.load();
//        Map<String, String> addr2fun = new HashMap<String, String>();
//        List<Function> functions = module.getFunctions();
//        Map<String, ReilFunction> funcs = new HashMap<String, ReilFunction>();
////        List<ReilFunction> funcs = new ArrayList<ReilFunction>();
//        for (Function f : functions) {
////            f.load();
//            ReilFunction fun = f.getReilCode();
//            funcs.put(fun.getName(), fun);
////            funcs.add(fun);
//        }
//        return funcs;
//    }

    public static List<ReilInstruction> getInstructions(Function function) throws InternalTranslationException, com.google.security.zynamics.binnavi.API.disassembly.CouldntLoadDataException {
        function.load();
        ReilFunction fun = function.getReilCode();
        List<ReilBlock> reilNodes = fun.getGraph().getNodes();
        List<ReilInstruction> instructions = new ArrayList<ReilInstruction>();
        for (ReilBlock node : reilNodes) {
            List<ReilInstruction> rInstructions = node.getInstructions();
            instructions.addAll(rInstructions);
        }
        return instructions;
    }

    public static List<ReilBlock> getBlocks(Function function) throws com.google.security.zynamics.binnavi.API.disassembly.CouldntLoadDataException, InternalTranslationException {
        function.load();
        ReilFunction fun = function.getReilCode();
        List<ReilBlock> reilNodes = fun.getGraph().getNodes();
        return reilNodes;
    }
}
