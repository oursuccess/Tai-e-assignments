/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Objects;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        //in中的每个参数默认为NAC, 而不能是UNDEF, 因这些参数是input/之前传入的, 不可能是UNDEF, 也不能保证是Constant
        //我们尚未处理方法调用, 因此将每个方法中的参数均视为NAC即可
        CPFact res = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            res.update(var, Value.getNAC());
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, val1) -> {
            target.update(var, meetValue(val1, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value val1, Value val2) {
        if (val2 == Value.getNAC() || val1 == val2 || val1 == Value.getUndef()) return val2;
        else if (val1 == Value.getNAC()) return Value.getNAC();
        else if (val2 == Value.getUndef()) return val1;
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        //out = gen U (in - {x, _}), x is def of stmt
        CPFact tmp = in.copy();
        if (stmt.getDef().isPresent()) {
            LValue def = stmt.getDef().get();
            if (def instanceof Var var) {
                int lastIndex = stmt.getUses().size() - 1;
                tmp.update(
                        var,
                        Objects.requireNonNull(evaluate(stmt.getUses().get(lastIndex), in)));
            }
        }

        return out.copyFrom(tmp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        }
        else if (exp instanceof IntLiteral intExp) {
            return Value.makeConstant(intExp.getValue());
        }
        else if (exp instanceof BinaryExp biExp) {
            Var var1 = biExp.getOperand1();
            Value value1 = in.get(var1);
            Var var2 = biExp.getOperand2();
            Value value2 = in.get(var2);
            if (!(value1.isConstant() && value2.isConstant())) return Value.getNAC();
            int int1 = value1.getConstant();
            int int2 = value2.getConstant();

            String op = biExp.getOperator().toString();
            switch (op) {
                //arithmetic
                case "+":
                    return Value.makeConstant(int1 + int2);
                case "-":
                    return Value.makeConstant(int1 - int2);
                case "*":
                    return Value.makeConstant(int1 * int2);
                case "/":
                    return int2 == 0 ? Value.getUndef() : Value.makeConstant(int1 / int2);
                case "%":
                    return int2 == 0 ? Value.getUndef() : Value.makeConstant(int1 % int2);
                //shift
                case ">>":
                    return Value.makeConstant(int1 >> int2);
                case "<<":
                    return Value.makeConstant(int1 << int2);
                //bitwise
                case "&":
                    return Value.makeConstant(int1 & int2);
                case "|":
                    return Value.makeConstant(int1 | int2);
                case "^":
                    return Value.makeConstant(int1 ^ int2);
                //condition
                case ">":
                    return Value.makeConstant(int1 > int2 ? 1 : 0);
                case "<":
                    return Value.makeConstant(int1 < int2 ? 1 : 0);
                case ">=":
                    return Value.makeConstant(int1 >= int2 ? 1 : 0);
                case "<=":
                    return Value.makeConstant(int1 <= int2 ? 1 : 0);
                case "==":
                    return Value.makeConstant(int1 == int2 ? 1 : 0);
                case "!=":
                    return Value.makeConstant(int1 != int2 ? 1 : 0);
                //default
                default:
                    break;
            }
        }
        return Value.getNAC();
    }
}
