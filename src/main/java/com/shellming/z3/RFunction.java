package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Address;
import com.google.security.zynamics.binnavi.API.disassembly.Function;
import com.google.security.zynamics.binnavi.API.reil.*;

import java.util.*;

/**
 * Created by ruluo1992 on 11/27/2016.
 */
public class RFunction {
    private Function function;
    private String funName;

    public RFunction(Function function) {
        this.function = function;
        this.funName = function.getName();
    }

    public String getFunName() {
        return funName;
    }

    private void addReg(ReilOperand operand, List<String> regs) {
        if (operand != null && operand.getType() == OperandType.REGISTER) {
            if (!regs.contains(operand.toString())) {
                regs.add(operand.toString());
            }
        }
    }

    public int getParamNum() {
        return 1;
    }

}
