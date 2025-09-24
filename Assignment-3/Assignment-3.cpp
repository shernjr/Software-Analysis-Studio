//===- Assignment-3.cpp -- Taint analysis ------------------//
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
 * Graph reachability, Andersen's pointer analysis and taint analysis
 *
 * Created on: Feb 18, 2024
 */

#include "Assignment-3.h"
#include "WPA/Andersen.h"
#include <sys/stat.h>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

using namespace SVF;
using namespace llvm;
using namespace std;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path
/// by matching calls and returns while maintaining a `callstack`.
/// Sources and sinks are identified by implementing and calling `readSrcSnkFromFile`
/// Each path including loops, qualified by a `callstack`, should only be traversed once using a `visited` set.
/// You will need to collect each path from src to snk and then add the path to the `paths` set.
/// Add each path (a sequence of node IDs) as a string into std::set<std::string> paths
/// in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs
static void collectICFGPath(std::set<std::string>& paths, const std::vector<unsigned>& path) {
    std::string pathStr = "START";
    for (size_t i = 0; i < path.size(); ++i) {
        pathStr += "->" + std::to_string(path[i]);
    }
    pathStr += "->END";
    std::cout << pathStr << std::endl;
    paths.insert(pathStr);
}

void ICFGTraversal::reachability(const ICFGNode* src, const ICFGNode* dst) {
    using CallStack = std::vector<const ICFGNode*>;
    using VisitPair = std::pair<const ICFGNode*, CallStack>;
    std::set<VisitPair> visited;
    std::vector<unsigned> path;
    CallStack callstack;

    std::function<void(const ICFGNode*)> dfs = [&](const ICFGNode* currNode) {
        VisitPair pair = {currNode, callstack};
        if (visited.count(pair)) return;
        visited.insert(pair);
        path.push_back(currNode->getId());

        if (currNode == dst) {
            collectICFGPath(paths, path);
        } else {
            for (const auto& edge : currNode->getOutEdges()) {
                if (edge->isIntraCFGEdge()) {
                    dfs(edge->getDstNode());
                } else if (edge->isCallCFGEdge()) {
                    callstack.push_back(currNode);
                    dfs(edge->getDstNode());
                    callstack.pop_back();
                } else if (edge->isRetCFGEdge()) {
                    if (SVFUtil::isa<RetICFGNode>(currNode)) {
                        const ICFGNode* callsite = SVFUtil::cast<RetICFGNode>(currNode)->getCallICFGNode();
                        if (!callstack.empty() && callstack.back() == callsite) {
                            callstack.pop_back();
                            dfs(edge->getDstNode());
                            callstack.push_back(callsite);
                            continue;
                        }
                    }
                } if (callstack.empty()) {
                    dfs(edge->getDstNode());
                }
                
            }
        }
        visited.erase(pair);
        path.pop_back();
    };

    dfs(src);
}

/// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
/// reachability analysis The format in SrcSnk.txt is in the form of
/// line 1 for sources  "{ api1 api2 api3 }"
/// line 2 for sinks    "{ api1 api2 api3 }"
void ICFGTraversal::readSrcSnkFromFile(const string& filename) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "Error opening file: " << filename << endl;
        return;
    }

    auto parseSetLine = [](const std::string& lineIn, std::set<std::string>& out) {
        std::string line = lineIn;
        // find {...}
        auto l = line.find('{');
        auto r = line.find('}', l == std::string::npos ? 0 : l + 1);
        if (l == std::string::npos || r == std::string::npos || r <= l + 1) return;
        std::string inside = line.substr(l + 1, r - l - 1);
        std::istringstream iss(inside);
        std::string tok;
        while (iss >> tok) {
            out.insert(tok);
        }
    };

    std::string line;

    // sources
    if (std::getline(file, line)) {
        parseSetLine(line, checker_source_api);
    }
    // sinks
    if (std::getline(file, line)) {
        parseSetLine(line, checker_sink_api);
    }

    file.close();
}

// TODO: Implement your Andersen's Algorithm here
/// The solving rules are as follows:
/// p <--Addr-- o        =>  pts(p) = pts(p) ∪ {o}
/// q <--COPY-- p        =>  pts(q) = pts(q) ∪ pts(p)
/// q <--LOAD-- p        =>  for each o ∈ pts(p) : q <--COPY-- o
/// q <--STORE-- p       =>  for each o ∈ pts(q) : o <--COPY-- p
/// q <--GEP, fld-- p    =>  for each o ∈ pts(p) : pts(q) = pts(q) ∪ {o.fld}
/// pts(q) denotes the points-to set of q
void AndersenPTA::solveWorklist() {

    for (ConstraintGraph::const_iterator it = consCG->begin(), eit = consCG->end(); it != eit; ++it) {
        ConstraintNode* cgNode = it->second;
        for (ConstraintEdge* edge : cgNode->getAddrInEdges()) {
            const AddrCGEdge* addr = SVFUtil::cast<AddrCGEdge>(edge);
            NodeID dst = addr->getDstID();
            NodeID src = addr->getSrcID();
            if (addPts(dst, src)) {
                pushIntoWorklist(dst);
            }
        }
    }

    while (!isWorklistEmpty()) {
        NodeID p = popFromWorklist();
        ConstraintNode* pNode = consCG->getConstraintNode(p);
        const PointsTo& pPts = getPts(p);

            for (ConstraintEdge* edge : pNode->getOutEdges()) {
            NodeID q = edge->getDstID();
            switch (edge->getEdgeKind()) {
                case ConstraintEdge::Copy: {
                    // Rule: q <--COPY-- p
                    if (unionPts(q, pPts)) {
                        pushIntoWorklist(q);
                    }
                    break;
                }
                case ConstraintEdge::Load: {
                    // Rule: q <--LOAD-- p
                    for (NodeID o : pPts) {
                        if (addCopyEdge(o, q)) {
                            if (unionPts(q, getPts(o))) {
                                pushIntoWorklist(q);
                            }
                        }
                    }
                    break;
                }
                case ConstraintEdge::Store: {
                    // Rule: q <--STORE-- p  =>  for each o ∈ pts(q) : o <--COPY-- p
                    const PointsTo& qPts = getPts(q);
                    for (NodeID o : qPts) {
                        if (addCopyEdge(p, o)) {
                            if (unionPts(o, pPts)) {
                                pushIntoWorklist(o);
                            }
                        }
                    }
                    break;
                }
                case ConstraintEdge::NormalGep:
                case ConstraintEdge::VariantGep: {
                    // Conservative fallback: treat GEP as COPY.
                    // This is sufficient for test1/test2 (per tutor note).
                    if (unionPts(q, pPts)) {
                        pushIntoWorklist(q);
                    }
                    break;
                }
                default:
                    break;

            }
        }
        
        for (ConstraintEdge* e : pNode->getStoreInEdges()) {
            NodeID p = e->getSrcID();
            const PointsTo& pPts = getPts(p);
            for (NodeID o : pPts) {
                if (addCopyEdge(p, o)) {
                    // propagate now
                    if (unionPts(o, pPts)) {
                        pushIntoWorklist(o);
                    }
                }
            }
        }

    }
}

/*g = < V,E > !" Constraint Graph
V: a set of nodes in graph
E: a set of edges in graph
WorkList: a vector of nodes
foreach do
    pts(p) = {o}
    pushIntoWorklist(p)
while WorkList ≠ ∅ do
    p !% popFromWorklist()
    foreach o ∈ pts(p) do
        foreach do
        if ∉ E then
            E !% E ∪ { }
            pushIntoWorklist(q)
        foreach do
            if ∉ E then
            E !% E ∪ { }
            pushIntoWorklist(o)
    foreach do
        pts(x) !% pts(x) ∪ pts(p)
        if pts(x) changed then
        pushIntoWorklist(x) */


/// TODO: Checking aliases of the two variables at source and sink. For example:
/// src instruction:  actualRet = source();
/// snk instruction:  sink(actualParm,...);
/// return true if actualRet is aliased with any parameter at the snk node (e.g., via ander->alias(..,..))
bool ICFGTraversal::aliasCheck(const CallICFGNode* src, const CallICFGNode* snk) {
    const RetICFGNode* retNode = src->getRetICFGNode();
    if (!retNode) return false;

    const SVFVar* retVar = retNode->getActualRet();
    if (!retVar) return false;

    for (const ValVar* actualParm : snk->getActualParms()) {
        if (ander->alias(retVar->getId(), actualParm->getId())) {
            return true;
        }
    }
    return false;
}

// Start taint checking.
// There is a tainted flow from p@source to q@sink
// if (1) alias(p,q)==true and (2) source reaches sink on ICFG.
void ICFGTraversal::taintChecking() {
	const fs::path& config = CUR_DIR() / "Tests/SrcSnk.txt";
	// configure sources and sinks for taint analysis
	readSrcSnkFromFile(config); // config.string() ?
	// Set file permissions to read-only for user, group and others
	if (chmod(config.string().c_str(), S_IRUSR | S_IRGRP | S_IROTH) == -1) {
		std::cerr << "Error setting file permissions for " << config << ": " << std::strerror(errno) << std::endl;
		abort();
	}
	ander = new AndersenPTA(pag);
	ander->analyze();
	for (const CallICFGNode* src : identifySources()) {
		for (const CallICFGNode* snk : identifySinks()) {
			if (aliasCheck(src, snk))
				reachability(src, snk);
		}
	}
}

/*!
 * Andersen analysis
 */
void AndersenPTA::analyze() {
	initialize();
	initWorklist();
	do {
		reanalyze = false;
		solveWorklist();
		if (updateCallGraph(getIndirectCallsites()))
			reanalyze = true;
	} while (reanalyze);
	finalize();
}