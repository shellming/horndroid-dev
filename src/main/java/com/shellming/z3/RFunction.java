package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Address;
import com.google.security.zynamics.binnavi.API.reil.*;

import java.util.*;

/**
 * Created by ruluo1992 on 11/27/2016.
 */
public class RFunction {
    private ReilFunction function;
    private List<String> regs;
    private Map<String, Integer> reg2idx;
    private Long funAddr;
    private String funName;

    public RFunction(ReilFunction function) {
        this.function = function;
        List<ReilBlock> blocks = function.getGraph().getNodes();
        funAddr = Long.MAX_VALUE;
        regs = new ArrayList<>();
        reg2idx = new HashMap<>();
        funName = function.getName();

        for (ReilBlock block : blocks) {
            Address address = block.getAddress();
            if (address.toLong() < funAddr) {
                funAddr = address.toLong();
            }
            List<ReilInstruction> instructions = block.getInstructions();
            for (ReilInstruction instruction : instructions) {
                addReg(instruction.getFirstOperand(), regs);
                addReg(instruction.getSecondOperand(), regs);
                addReg(instruction.getThirdOperand(), regs);
            }
        }
        for (int i = 0; i < regs.size(); i++) {
            reg2idx.put(regs.get(i), i);
        }
    }

    private void addReg(ReilOperand operand, List<String> regs) {
        if (operand != null && operand.getType() == OperandType.REGISTER) {
            if (!regs.contains(operand.toString())) {
                regs.add(operand.toString());
            }
        }
    }

    public String getFunName() {
        return funName;
    }

    public void setFunName(String funName) {
        this.funName = funName;
    }

    public int getRegNums() {
        return regs.size();
    }

    public Integer getRegIdx(String reg) {
        return reg2idx.get(reg);
    }
}
