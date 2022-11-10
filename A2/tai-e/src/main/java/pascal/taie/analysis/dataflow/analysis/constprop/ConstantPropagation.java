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

import org.yaml.snakeyaml.scanner.Constant;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        // TODO - finish me
        IR ir = cfg.getIR();
        CPFact entryFact = newInitialFact();
        for(Var var : ir.getParams())
        {
            if(canHoldInt(var))
                entryFact.update(var,Value.getNAC());
        }
        return entryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var:fact.keySet())
        {
            target.update(var,meetValue(fact.get(var),target.get(var)));
        }

    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()||v2.isNAC()) return v1.getNAC();
        else if(v1.isConstant()&&v2.isUndef()) return v1;
        else if(v2.isConstant()&&v1.isUndef()) return v2;
        else if(v1.equals(v2)) return v1;
        return v1.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        if (stmt instanceof DefinitionStmt def)
        {
            if(def.getLValue() instanceof Var lvar){
                Exp rexp = def.getRValue();
                boolean flag=false;
                for (Var invar : in.keySet()) {
                    if (!invar.equals(lvar)) {
                        flag |= out.update(invar, in.get(invar));
                    }
                }
                if(canHoldInt(lvar))
                    flag|=out.update(lvar,evaluate(rexp,in));
                return flag;

            }



        }
        return out.copyFrom(in);
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
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var) {
            return in.get((Var)exp);
        } else if (exp instanceof BinaryExp) {
            BinaryExp binary=(BinaryExp)exp;
            BinaryExp.Op op = binary.getOperator();
            Value v1 = evaluate(binary.getOperand1(), in);
            Value v2 = evaluate(binary.getOperand2(), in);
            if(v2.isConstant() && v2.getConstant()==0)
            {
                if(op instanceof ArithmeticExp.Op)
                {
                    BinaryExp.Op tem = (ArithmeticExp.Op) op;
                    if(tem==ArithmeticExp.Op.REM || tem==ArithmeticExp.Op.DIV) return Value.getUndef();
                }
            }
            if (v1.isConstant() && v2.isConstant()) {
                int i1 = v1.getConstant();
                int i2 = v2.getConstant();
                int tmp=0;
                if (op instanceof ArithmeticExp.Op)
                {
                    ArithmeticExp.Op tem = (ArithmeticExp.Op) op;
                    if(tem==ArithmeticExp.Op.ADD) tmp=i1+i2;
                    else if(tem==ArithmeticExp.Op.SUB) tmp=i1-i2;
                    else if(tem==ArithmeticExp.Op.DIV) tmp=i1/i2;
                    else if(tem==ArithmeticExp.Op.MUL) tmp=i1*i2;
                    else if(tem==ArithmeticExp.Op.REM) tmp=i1%i2;
                }
                else if (op instanceof ConditionExp.Op)
                {
                    ConditionExp.Op tem = (ConditionExp.Op) op;
                    if(tem==ConditionExp.Op.EQ) tmp=i1 == i2 ? 1 : 0;
                    else if(tem==ConditionExp.Op.GE) tmp=i1 >= i2 ? 1 : 0;
                    else if(tem==ConditionExp.Op.LT) tmp=i1 < i2 ? 1 : 0;
                    else if(tem==ConditionExp.Op.GT) tmp=i1 > i2 ? 1 : 0;
                    else if(tem==ConditionExp.Op.LE) tmp=i1 <= i2 ? 1 : 0;
                    else if(tem==ConditionExp.Op.NE) tmp=i1 != i2 ? 1 : 0;
                }
                else if (op instanceof ShiftExp.Op)
                {
                    ShiftExp.Op tem = (ShiftExp.Op) op;
                    if(tem==ShiftExp.Op.SHL) tmp=i1<<i2;
                    else if(tem==ShiftExp.Op.SHR) tmp=i1>>i2;
                    else if(tem==ShiftExp.Op.USHR) tmp=i1>>>i2;
                }
                else if (op instanceof BitwiseExp.Op)
                {
                    BitwiseExp.Op tem = (BitwiseExp.Op) op;
                    if(tem==BitwiseExp.Op.OR) tmp=i1|i2;
                    else if(tem==BitwiseExp.Op.AND) tmp=i1&i2;
                    else if(tem==BitwiseExp.Op.XOR) tmp=i1^i2;
                }
                return Value.makeConstant(tmp);
            } else if (v1.isNAC() || v2.isNAC())
            {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();

    }

}
