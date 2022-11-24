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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.util.WorkList;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        callGraph.addEntryMethod(entry);
        Queue<JMethod> wl = new ArrayDeque<>();
        wl.add(entry);
        while(!wl.isEmpty())
        {
            JMethod m = wl.remove();
            if(callGraph.addReachableMethod(m));
            for(Invoke cs: callGraph.getCallSitesIn(m))
            {
                Set<JMethod> T = resolve(cs);
                for(JMethod m_:T)
                {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs),cs,m_));
                    wl.add(m_);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodref = callSite.getMethodRef();
        Subsignature m = methodref.getSubsignature();
        if(callSite.isStatic())
        {
            T.add(methodref.getDeclaringClass().getDeclaredMethod(m));
        }
        else if(callSite.isSpecial())
        {
            JClass cm = methodref.getDeclaringClass();
            JMethod tmp = dispatch(cm,m);
            if(tmp!=null)
                T.add(tmp);
        }
        else
        {
            Queue<JClass> queue = new LinkedList<>();
            queue.add(methodref.getDeclaringClass());
            while(!queue.isEmpty())
            {
                JClass c = queue.poll();
                JMethod tmp = dispatch(c,m);
                if(tmp!=null)
                    T.add(tmp);
                if(c.isInterface())
                {
                    queue.addAll(hierarchy.getDirectImplementorsOf(c));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(c));
                }
                else {
                    queue.addAll(hierarchy.getDirectSubclassesOf(c));
                }
            }


        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass == null) return null;
        JMethod tem = jclass.getDeclaredMethod(subsignature);
        if(tem!=null&&!tem.isAbstract()) return tem;
        else{
            JClass superclass = jclass.getSuperClass();
            if(superclass!=null)
                return dispatch(superclass,subsignature);
            return null;
        }

    }
}
