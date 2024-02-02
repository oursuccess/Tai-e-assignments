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

import pascal.taie.Assignment;
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

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.Set;
import java.util.HashSet;
import java.util.TreeSet;

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
        //按序访问stmt(bfs)
        ArrayDeque<Stmt> stmts = new ArrayDeque<>();
        //记录可达的Stmt
        Set<Stmt> reachable = new HashSet<>();
        //记录已经访问的Stmt
        Set<Stmt> visited = new HashSet<>();

        stmts.addLast(cfg.getEntry());  //第一个访问节点为入口
        //方法的入口与出口必然可达(不考虑因while循环导致不可出的情况)
        reachable.add(cfg.getEntry());
        reachable.add(cfg.getExit());
        //bfs
        while (!stmts.isEmpty()) {
            Stmt stmt = stmts.pollFirst();
            visited.add(stmt);  //已访问到
            if (stmt instanceof AssignStmt assign) {    //赋值语句, 检查是否为无用赋值
                //后继语句可直接加入队列
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!visited.contains(succ)) stmts.addLast(succ);   //防止重复访问
                }

                //死代码: 左值变量未使用, 且右值无副作用
                if (!(assign.getLValue() instanceof Var var
                        && !liveVars.getResult(assign).contains(var)
                        && hasNoSideEffect(assign.getRValue())))
                    reachable.add(assign);  //否则, 在可达代码中加入之. 我们未处理由于下一语句不可达而导致本语句也不再live的情况
            } else if (stmt instanceof If ifStmt) { //if语句处理, 检查是否有不可达分支
                reachable.add(stmt);    //if语句永远可走到
                Value eval = ConstantPropagation.evaluate(  //if条件表达式
                        ifStmt.getCondition(),
                        constants.getResult(ifStmt));
                if (!eval.isConstant()) {
                    for (Stmt succ : cfg.getSuccsOf(stmt)) {
                        if (!visited.contains(succ)) stmts.addLast(succ);
                    }
                } else {    //永远只走true/false一边
                    Edge.Kind targetKind = eval.getConstant() == 1 ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == targetKind && !visited.contains(edge.getTarget()))
                            stmts.addLast(edge.getTarget());
                    }
                }
            } else if (stmt instanceof SwitchStmt switchStmt) {
                reachable.add(stmt);
                Value var = constants.getResult(switchStmt).get(switchStmt.getVar());
                if (var.isConstant()) { //仅执行常数对应的边
                    int target = var.getConstant();
                    boolean matched =  false;   //可能有default分支
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == target) {
                            matched = true;
                            if (!visited.contains(edge.getTarget())) stmts.addLast(edge.getTarget());
                        }
                    }
                    if (!matched) { //default分支
                        Stmt defaultStmt = switchStmt.getDefaultTarget();
                        if (!visited.contains(defaultStmt)) stmts.addLast(defaultStmt);
                    }
                } else {    //均可能执行
                    for (Stmt succ : cfg.getSuccsOf(stmt)) {
                        if (!visited.contains(succ)) stmts.addLast(succ);
                    }
                }
            } else {    //其它类型语句, 直接可达
                reachable.add(stmt);
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!visited.contains(succ)) stmts.addLast(succ);
                }
            }
        }

        for (Stmt stmt : ir.getStmts()) {
            if (!reachable.contains(stmt)) deadCode.add(stmt);
        }

        return deadCode;
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
