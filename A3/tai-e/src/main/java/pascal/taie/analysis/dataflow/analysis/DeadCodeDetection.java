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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import soot.jimple.toolkits.scalar.Evaluator;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Queue<Stmt> queue = new ArrayDeque<>();
        queue.add(cfg.getEntry());
        Set<Stmt> marked = new HashSet<>();
        while(!queue.isEmpty())
        {
            Stmt stmt = queue.remove();
            marked.add(stmt);
            if(stmt instanceof AssignStmt<?,?> assign)
            {
                if(assign.getLValue() instanceof Var lhs)
                {
                    if(!liveVars.getOutFact(assign).contains(lhs)&&hasNoSideEffect(assign.getRValue()))
                    {
                        deadCode.add(stmt);
                    }
                }
            }
            for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt))
            {
                if(!isUnreach(edge,constants))
                {
                    Stmt suc = edge.getTarget();
                    if(!marked.contains(suc)) queue.add(suc);
                }
            }
        }
        if (marked.size() < cfg.getNumberOfNodes())
        {
            for (Stmt s : ir)
            {
                if (!marked.contains(s))
                {
                    deadCode.add(s);
                }
            }
        }
        return deadCode;
    }
    boolean isUnreach(Edge<Stmt> edge,DataflowResult<Stmt,CPFact> constants)
    {
        Stmt src=edge.getSource();
        if(src instanceof  If ifstmt)
        {
            Value val = ConstantPropagation.evaluate(ifstmt.getCondition(), constants.getInFact(ifstmt));
            if(val.isConstant())
            {
                int v = val.getConstant();
                if((v==1&&edge.getKind()== Edge.Kind.IF_FALSE)||(v==0&&edge.getKind()== Edge.Kind.IF_TRUE))
                {
                    return true;
                }
            }
        }
        else if (src instanceof SwitchStmt switchstmt)
        {
            Value val = ConstantPropagation.evaluate(switchstmt.getVar(),constants.getInFact(switchstmt));
            if(val.isConstant())
            {
                int v = val.getConstant();
                if(edge.isSwitchCase())
                {
                    if(v!=edge.getCaseValue())
                    {
                        return true;
                    }
                }
                else
                {
                    for(int x:switchstmt.getCaseValues())
                    {
                        if(x==v)
                        {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }


    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
