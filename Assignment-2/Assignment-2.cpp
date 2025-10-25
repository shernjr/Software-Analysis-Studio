//===- SVF-Teaching Assignment 2-------------------------------------//
//
//     SVF: Static Value-Flow Analysis Framework for Source Code
//
// Copyright (C) <2013->
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//
/*
 // SVF-Teaching Assignment 2 : Source Sink ICFG DFS Traversal
 //
 // 
 */

#include <set>
#include "Assignment-2.h"
#include <iostream>
using namespace SVF;
using namespace std;

/// TODO: print each path once this method is called, and
/// add each path as a string into std::set<std::string> paths
/// Print the path in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs

void ICFGTraversal::collectICFGPath(std::vector<unsigned> &path){
    std::string pathStr = "START";
    for (size_t i = 0; i < path.size(); ++i) { 
        pathStr += "->" + std::to_string(path[i]); // double check
    }
    pathStr += "->END";
    std::cout << pathStr << std::endl;
    paths.insert(pathStr);
}


// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from src to dst

void ICFGTraversal::reachability(const ICFGNode *src, const ICFGNode *dst)
{
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
            collectICFGPath(path);
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

/**
     * reachability(curNode, snk)
        pair = ⟨curNode, callstack⟩;
        if pair ∈ visited then
        return;

        visited.insert(pair);
        path.push back(curNode);

        if src == snk then
            collectICFGPath(path);
        foreach edge ∈ curNode.getOutEdges() do
            if edge.isIntraCFGEdge() then
                reachability(edge.dst, snk);
            else if edge.isCallCFGEdge() then
                callstack.push back(edge.src);
                reachability(edge.dst, snk);
                callstack.pop back();
            else if edge.isRetCFGEdge() then
                if callstack ̸= ∅ && callstack.back() == edge.getCallSite() then
                    callstack.pop back();
                    reachability(edge.dst, snk);
                    callstack.push back(edge.getCallSite());
            else if callstack == ∅ then
                reachability(edge.dst, snk);
        
        visited.erase(pair);
        path.pop back();

     */