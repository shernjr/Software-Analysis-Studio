//===- Assignment-4.cpp -- Automated assertion-based verification (Static symbolic execution) --//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//
/*
 * Automated assertion-based verification (Static symbolic execution)
 *
 * Created on: Feb 19, 2024
 */

#include "Assignment-4.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from
/// You will need to collect each path from src node to snk node and then add the path to the `paths` set by
/// calling the `collectAndTranslatePath` method which is then trigger the path translation.
/// This implementation, slightly different from Assignment-1, requires ICFGNode* as the first argument.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* sink) {
	// Current node is always the destination of the incoming edge
	const ICFGNode* curNode = curEdge->getDstNode();

	// Record visitation state keyed by (edge, callstack) to ensure we traverse
	// each loop at most once per calling context
	ICFGEdgeStackPair key = {curEdge, callstack};
	if (visited.find(key) != visited.end()) return;
	visited.insert(key);

	// Maintain the current path of edges
	path.push_back(curEdge);

	// If we've reached the sink (assert callsite), collect and translate this path
	if (curNode == sink) {
		collectAndTranslatePath();
	} else {
		// DFS over outgoing edges with call/return matching via callstack
		for (const ICFGEdge* edge : curNode->getOutEdges()) {
			if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
				// Enter callee: push callsite into context stacks and continue
				const ICFGNode* callsite = callEdge->getSrcNode();
				callstack.push_back(callsite);
				pushCallingCtx(callsite);
				reachability(edge, sink);
				popCallingCtx();
				callstack.pop_back();
			}
			else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
				// Return to caller only if it matches the top of callstack
				const RetICFGNode* retDst = SVFUtil::cast<RetICFGNode>(retEdge->getDstNode());
				const ICFGNode* callsite = retDst->getCallICFGNode();
				if (!callstack.empty() && callstack.back() == callsite) {
					// Simulate return: pop context for traversal, recurse, then restore
					const ICFGNode* top = callstack.back();
					callstack.pop_back();
					popCallingCtx();
					reachability(edge, sink);
					// restore context after exploring this edge
					callstack.push_back(top);
					pushCallingCtx(top);
				}
				// else: unmatched return, skip
			}
			else {
				// Intra-procedural edge
				reachability(edge, sink);
			}
		}
	}

	// Backtrack
	path.pop_back();
	visited.erase(key);
}


/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set, (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible. (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path).
void SSE::collectAndTranslatePath() {
	// 1) Serialize and record the path for de-duplication/inspection
	if (path.empty()) return;
	std::string pathStr = "START";
	for (const ICFGEdge* e : path) {
		const ICFGNode* n = e->getDstNode();
		if (n) pathStr += "->" + std::to_string(n->getId());
	}
	pathStr += "->END";
	bool inserted = paths.insert(pathStr).second;

	// 2) Translate the path into Z3 constraints in an isolated solver frame
	getSolver().push();
	bool feasible = translatePath(path);

	// 3) If feasible, check the assertion at the last node of this path
	if (feasible) {
		const ICFGNode* lastNode = path.back()->getDstNode();
		assert(lastNode && "path should end at a valid node");
		assertchecking(lastNode);
	}

	// 4) Restore solver to pre-path state to avoid cross-path contamination
	getSolver().pop();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
	const ICFGNode* srcNode = calledge->getSrcNode();
    DBOP(std::cout << "\n## Analyzing " << srcNode->toString() << "\n");

    // 1) Capture actuals (RHS) in the caller context first
    std::vector<std::pair<NodeID, expr>> paramBindings;
    paramBindings.reserve(calledge->getCallPEs().size());
    for (const CallPE* callPE : calledge->getCallPEs()) {
        expr rhs = getZ3Expr(callPE->getRHSVarID()); // caller frame
        paramBindings.emplace_back(callPE->getLHSVarID(), rhs); // formal id + caller-evaluated actual
    }

    // 2) Switch to callee frame: push calling context + solver
    const ICFGNode* callsite = calledge->getSrcNode();
    pushCallingCtx(callsite);
    callstack.push_back(callsite);
    getSolver().push();

    // 3) Bind formals (callee frame) to captured actuals (caller frame)
    for (const auto& [lhsId, rhsFromCaller] : paramBindings) {
        expr lhs = getZ3Expr(lhsId); // now evaluated in callee frame
        addToSolver(lhs == rhsFromCaller);
    }
	/**
	 * 	callNode ← callEdge.getSrcNode();;
		FunEntryNode ←callEdge.getDstNode();
		getSolver().push();
		foreach callPE ∈ calledge.getCallPEs() do
			lhs ← getZ3Expr(callPE.getLHSVarID());;
			rhs ← getZ3Expr(callPE.getRHSVarID());;
			addToSolver(lhs == rhs);;
		return true;
	 */
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    DBOP(std::cout << "\n## Analyzing "<< retEdge->getDstNode()->toString() << "\n");

    FunExitICFGNode* FunExitNode = SVFUtil::cast<FunExitICFGNode>(retEdge->getSrcNode());
    RetICFGNode* retNode = SVFUtil::cast<RetICFGNode>(retEdge->getDstNode());

    // If there is a RetPE, evaluate the return expression under callee constraints
    expr rhs_eval = getCtx().int_val(0);  // unused default if no RetPE
    bool hasRet = false;
    if (const RetPE* retPE = retEdge->getRetPE()) {
        expr rhs_callee = getZ3Expr(retPE->getRHSVarID()); // callee frame
        rhs_eval = getEvalExpr(rhs_callee);                 // evaluate before pop
        hasRet = true;
    }

	// Pop solver and calling context to return to caller frame
	getSolver().pop();
	if (!callingCtx.empty()) popCallingCtx();
	if (!callstack.empty()) callstack.pop_back();

    // In caller frame, assign the evaluated return to the destination (if any)
    if (hasRet) {
        const RetPE* retPE = retEdge->getRetPE(); // safe to refer again
        expr lhs_caller = getZ3Expr(retPE->getLHSVarID()); // caller frame
        addToSolver(lhs_caller == rhs_eval);
    }

	/**
	 * rhs(getCtx());;
	 * if retPE ← retEdge.getRetPE() then
	 * rhs ← getZ3Expr(retPE.getRHSVarID());;
	 * getSolver().pop();;
	 * if retPE ← retEdge.getRetPE() then
	 * lhs ← getZ3Expr(retPE.getLHSVarID());;
	 * addToSolver(lhs == rhs);;
	 * return true;;
	 */
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given branch on the ICFG looks like the following:
///       	     ICFGNode1 (condition %cmp)
///       	     1	/    \  0
///       	  ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition())->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    assert(edge->getCondition() && "not a conditional control-flow transfer?");
    expr cond = getZ3Expr(edge->getCondition()->getId());
    expr successorVal = getCtx().int_val((int) edge->getSuccessorCondValue());

    expr res = getEvalExpr(cond == successorVal);
    
    if (res.is_false()) {
        // Path is provably infeasible (i.e., prior constraints entail cond != successorVal)
        return false;
    } 
    // If it's true or indeterminate (res is the original expression), we add the constraint
    else {
        addToSolver(cond == successorVal);
        return true;
    }

		/**
	 * 	cond = intraEdge.getCondition();
		successorVal = intraEdge.getSuccessorCondValue();
		res = getEvalExpr(cond == successorVal);
		if res.is false() then
			addToSolver(cond! = successorVal);
			return false;
		else if res.is true() then
			addToSolver(cond == successorVal);
			return true;
		else
			return true;
		return true;
	 */
}

/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
/// Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt, BinaryOPStmt, CmpStmt, SelectStmt, and PhiStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
	const ICFGNode* dstNode = edge->getDstNode();
	const ICFGNode* srcNode = edge->getSrcNode();
	DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

	for (const SVFStmt *stmt : dstNode->getSVFStmts())
	{
		if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
		{
			// TODO: Implement handling of AddrStmt
			expr obj = getMemObjAddress(addr->getRHSVarID());
			expr lhs = getZ3Expr(addr->getLHSVarID());
			addToSolver(obj == lhs);
		}
		else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
		{
			// TODO: Implement handling of CopyStmt
			expr lhs = getZ3Expr(copy->getLHSVarID());
			expr rhs = getZ3Expr(copy->getRHSVarID());
			addToSolver(rhs == lhs);
		}
		else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
		{
			// TODO: Implement handling of LoadStmt
			expr lhs = getZ3Expr(load->getLHSVarID());
			expr rhs = getZ3Expr(load->getRHSVarID());
			addToSolver(lhs == z3Mgr->loadValue(rhs));
		}
		else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
		{
			// TODO: Implement handling of StoreStmt
			expr lhs = getZ3Expr(store->getLHSVarID());
			expr rhs = getZ3Expr(store->getRHSVarID());
			z3Mgr->storeValue(lhs, rhs);
		}
		else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
		{
			// TODO: Implement handling of GepStmt
			expr lhs = getZ3Expr(gep->getLHSVarID());
			expr rhs = getZ3Expr(gep->getRHSVarID());
    		expr offset = getCtx().int_val(z3Mgr->getGepOffset(gep, callstack));
			expr gepAddr = z3Mgr->getGepObjAddress(rhs, offset);
			addToSolver(lhs == gepAddr);
		}
		/// Given a CmpStmt "r = a > b"
		/// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
		/// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
		/// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
		/// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
		/// We assume integer-overflow-free in this assignment
		else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
		{
			// TODO: Implement handling of CmpStmt
			expr op0 = getZ3Expr(cmp-> getOpVarID(0));
			expr op1 = getZ3Expr(cmp-> getOpVarID(1));
			expr res = getZ3Expr(cmp-> getResID());
			switch (cmp->getPredicate()) {
				case CmpStmt::ICMP_EQ:
					addToSolver(res == ite(op0 == op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				case CmpStmt::ICMP_NE:
					addToSolver(res == ite(op0 != op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				case CmpStmt::ICMP_UGT:
				case CmpStmt::ICMP_SGT:
					addToSolver(res == ite(op0 > op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				case CmpStmt::ICMP_UGE:
				case CmpStmt::ICMP_SGE:
					addToSolver(res == ite(op0 >= op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				case CmpStmt::ICMP_ULT:
				case CmpStmt::ICMP_SLT:
					addToSolver(res == ite(op0 < op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				case CmpStmt::ICMP_ULE:
				case CmpStmt::ICMP_SLE:
					addToSolver(res == ite(op0 <= op1, getCtx().int_val(1), getCtx().int_val(0)));
					break;
				default:
					assert(false && "Unknown CmpStmt predicate");
			}
		}
		else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
		{
			expr op0 = getZ3Expr(binary->getOpVarID(0));
			expr op1 = getZ3Expr(binary->getOpVarID(1));
			expr res = getZ3Expr(binary->getResID());
			switch (binary->getOpcode())
			{
			case BinaryOperator::Add:
				addToSolver(res == op0 + op1);
				break;
			case BinaryOperator::Sub:
				addToSolver(res == op0 - op1);
				break;
			case BinaryOperator::Mul:
				addToSolver(res == op0 * op1);
				break;
			case BinaryOperator::SDiv:
				addToSolver(res == op0 / op1);
				break;
			case BinaryOperator::SRem:
				addToSolver(res == op0 % op1);
				break;
			case BinaryOperator::Xor:
				addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
				break;
			case BinaryOperator::And:
				addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
				break;
			case BinaryOperator::Or:
				addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
				break;
			case BinaryOperator::AShr:
				addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
				break;
			case BinaryOperator::Shl:
				addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
				break;
			default:
				assert(false && "implement this part");
			}
		}
		else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
		{
			DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
		}
		else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
			expr res = getZ3Expr(select->getResID());
			expr tval = getZ3Expr(select->getTrueValue()->getId());
			expr fval = getZ3Expr(select->getFalseValue()->getId());
			expr cond = getZ3Expr(select->getCondition()->getId());
			addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
		}
		else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
			expr res = getZ3Expr(phi->getResID());
			bool opINodeFound = false;
			for(u32_t i = 0; i < phi->getOpVarNum(); i++){
				assert(srcNode && "we don't have a predecessor ICFGNode?");
				if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
				{
					expr ope = getZ3Expr(phi->getOpVar(i)->getId());
					addToSolver(res == ope);
					opINodeFound = true;
				}
			}
			assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
		}
	}

	return true;
}

/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
	for (const ICFGEdge* edge : path) {
		if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
			if (handleIntra(intraEdge) == false)
				return false;
		}
		else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
			handleCall(call);
		}
		else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
			handleRet(ret);
		}
		else
			assert(false && "what other edges we have?");
	}

	return true;
}

/// Program entry
void SSE::analyse() {
	for (const ICFGNode* src : identifySources()) {
		assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
		for (const ICFGNode* sink : identifySinks()) {
			const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
			/// start traversing from the entry to each assertion and translate each path
			reachability(&startEdge, sink);
			resetSolver();
		}
	}
}
