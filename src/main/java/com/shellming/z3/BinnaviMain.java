package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.*;
import com.google.security.zynamics.binnavi.API.reil.*;
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

import java.util.*;

/**
 * Created by ruluo1992 on 11/27/2016.
 */
public class BinnaviMain {
    public static void main(String[] args) throws LoadCancelledException, CouldntLoadDataException, InvalidDatabaseVersionException, CouldntConnectException, InvalidDatabaseException, CouldntLoadDriverException, InvalidExporterDatabaseFormatException, CouldntInitializeDatabaseException, com.google.security.zynamics.binnavi.API.disassembly.CouldntLoadDataException, InternalTranslationException {
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
        CDatabase db = new CDatabase(database.getDescription(), database.getDriver(),
                database.getHost(), database.getName(), database.getUser(), database.getPassword(),
                database.getIdentity(), database.isSavePassword(), database.isAutoConnect());
        manager.addDatabase(db);
        DatabaseManager dbManager = new DatabaseManager(manager);
        db.connect();
        db.load();
        Database apiDatabase = new Database(db);
        List<Module> modules = apiDatabase.getModules();
        for (Module module : modules) {
            module.load();
            Map<Long, String> addr2fun = new HashMap<Long, String>();
            List<Function> functions = module.getFunctions();
            for (Function f : functions) {
                Address address = f.getAddress();
                addr2fun.put(address.toLong() << 8, f.getName());
                ReilFunction reilFunction = f.getReilCode();
                System.out.println("function :" + f.getName());
//                System.out.println("native code start:");
//                List<BasicBlock> nodes = f.getGraph().getNodes();
//                for (BasicBlock node : nodes) {
//                    List<Instruction> instructions = node.getInstructions();
//                    for (Instruction instruction : instructions) {
//                        System.out.println(instruction.toString());
//                    }
//                }
//                System.out.println("native code done.");
                System.out.println("reil code start");
                List<ReilBlock> reilNodes = reilFunction.getGraph().getNodes();
                int regIndex = 0;
                Map<String, Integer> reg2idx = new HashMap<>();
                Set<String> regs = new HashSet<>();
                for (ReilBlock node : reilNodes) {
                    List<ReilInstruction> rInstructions = node.getInstructions();
                    for (ReilInstruction rInstruction : rInstructions) {
                        ReilOperand operand = rInstruction.getSecondOperand();
                        System.out.println(rInstruction);
                        System.out.println(rInstruction.getMnemonic());
                        OperandSize s = operand.getSize();
                        if (operand.getType() == OperandType.REGISTER) {
                            String name = operand.toString();
                            regs.add(name);
                        } else if (operand.getType() == OperandType.INTEGER_LITERAL) {
                            System.out.println("value:" + operand.getValue());
                        }
//                        System.out.println(rInstruction.toString());
                    }
                }
                System.out.println("reil code done.");
                System.out.println(regs);
                break;
            }
        }



    }
}
