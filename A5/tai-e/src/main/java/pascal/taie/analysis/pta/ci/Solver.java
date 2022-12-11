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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.addReachableMethod(method))
        {
            for(Stmt stmt: method.getIR().getStmts())
            {
                stmt.accept(stmtProcessor);
            }
        }

    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        private List<Stmt> S=new ArrayList<>();
//        private List<JMethod> RM=new ArrayList<>();
        public Void visit(New stmt) {


            Var x = stmt.getLValue();
            workList.addEntry(pointerFlowGraph.getVarPtr(x),new PointsToSet(heapModel.getObj(stmt)));

            return visitDefault(stmt);
        }
        public Void visit(Copy stmt)
        {
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(y),pointerFlowGraph.getVarPtr(x));
            return visitDefault(stmt);
        }
        public Void visit(LoadField stmt)
        {
            JField T_f = stmt.getFieldRef().resolve();
            if(T_f.isStatic())
            {
                Var y = stmt.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(T_f),pointerFlowGraph.getVarPtr(y));
            }
            return visitDefault(stmt);
        }
        public Void visit(StoreField stmt)
        {
            JField T_f = stmt.getFieldRef().resolve();
            if(T_f.isStatic())
            {
                Var y = stmt.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(y),pointerFlowGraph.getStaticField(T_f));
            }
            return visitDefault(stmt);
        }
        public Void visit(Invoke stmt)
        {


            if(stmt.isStatic())
            {
                JMethod method = resolveCallee(null,stmt);
                Var r = stmt.getResult();
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC,stmt,method)))
                {
                    addReachable(method);
                    int argCount = stmt.getInvokeExp().getArgCount();

                    IR ir = method.getIR();
                    for(int index=0;index<argCount;index++)
                    {
                        Var arg = stmt.getInvokeExp().getArg(index);
                        Var par = ir.getParam(index);
                        addPFGEdge(pointerFlowGraph.getVarPtr(arg),pointerFlowGraph.getVarPtr(par));


                    }
                    if(r!=null)
                    {
                        VarPtr varPtr = pointerFlowGraph.getVarPtr(r);
                        for(Var ret: ir.getReturnVars())
                        {
                            addPFGEdge(pointerFlowGraph.getVarPtr(ret), varPtr);
                        }
                    }

                }


            }
            return visitDefault(stmt);
        }
        public Void visitDefault(Stmt stmt)
        {
            S.add(stmt);
            return null;
        }


    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target))
        {
            PointsToSet pointsToSet = source.getPointsToSet();
            if(!pointsToSet.isEmpty())
            {
                workList.addEntry(target,pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty())
        {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n,pts);
            if(n instanceof VarPtr varPtr)
            {
                Var x = varPtr.getVar();
                for(Obj o:delta)
                {
                    for(StoreField f:x.getStoreFields())
                    {
                        if(!f.isStatic())
                        {
                            VarPtr y = pointerFlowGraph.getVarPtr(f.getRValue());
                            JField field = f.getFieldRef().resolve();
                            InstanceField o_f = pointerFlowGraph.getInstanceField(o, field);
                            addPFGEdge(y, o_f);
                        }

                    }
                    for(LoadField f:x.getLoadFields())
                    {
                        if(!f.isStatic())
                        {
                            VarPtr y = pointerFlowGraph.getVarPtr(f.getLValue());
                            JField field = f.getFieldRef().resolve();
                            InstanceField o_f = pointerFlowGraph.getInstanceField(o, field);
                            addPFGEdge(o_f, y);
                        }

                    }


                    // x[] = y
                    for (StoreArray storeArray : x.getStoreArrays()) {
                        VarPtr source = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        ArrayIndex target = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(source, target);
                    }
                    for (LoadArray loadArray : x.getLoadArrays()) {
                        VarPtr source = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        ArrayIndex target = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(target, source);
                    }

                    processCall(x,o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet difference = new PointsToSet();
        if(!pointsToSet.isEmpty())
        {

            PointsToSet ptn = pointer.getPointsToSet();
            for(Obj obj:pointsToSet)
            {
                if(!ptn.contains(obj))
                {
                    difference.addObject(obj);
                    ptn.addObject(obj);
                }



            }

            for(Pointer s:pointerFlowGraph.getSuccsOf(pointer))
            {
                workList.addEntry(s,difference);
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke invoke: var.getInvokes())
        {
            if(!invoke.isStatic())
            {
                JMethod m = resolveCallee(recv,invoke);
                Var r = invoke.getResult();
                IR ir = m.getIR();
//                if(r!=null){
                    workList.addEntry(pointerFlowGraph.getVarPtr(ir.getThis()),new PointsToSet(recv));
                    if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,m)))
                    {

                        addReachable(m);

                        int argCount = invoke.getInvokeExp().getArgCount();


                        for(int index=0;index<argCount;index++)
                        {
                            Var arg = invoke.getInvokeExp().getArg(index);
                            Var par = ir.getParam(index);
                            addPFGEdge(pointerFlowGraph.getVarPtr(arg),pointerFlowGraph.getVarPtr(par));


                        }
                        if(r!=null)
                        for(Var ret: ir.getReturnVars())
                        {
                            addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(r));
                        }

//                    }
                }
            }


        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
