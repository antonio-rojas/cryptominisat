#pragma once

#include <cstdint>
#include <vector>
#include <cassert>
#include <map>
#include <unordered_set>
#include <iostream>

#include "clause.h"
#include "prooflogging/ConstraintId.hpp"

using std::vector;
using std::unordered_set;
using std::ostream;
using std::map;
using namespace CMSat;


typedef uint32_t BDDNodeRef;

class BDDNode {
public:
    BDDNodeRef left = 0; // true
    BDDNodeRef right = 0; // false
    BDDNodeRef parent = 0; // false
    size_t var;
    ConstraintId constraintID = ConstraintId(0);
};

inline ostream& operator<< (ostream &out, const BDDNode &node) {
    out << "( l:" << node.left << " r:" << node.right
        << " p:" << node.parent << " var:" << node.var << " cId:" << node.constraintID << ")";
    return out;
}

class BDD {
public:
    vector<BDDNode> data;
    struct {
        size_t nOpen = 0;
    } stats;

    size_t nVars;
    bool rhs;

    size_t constraintCounter = 0;

    BDD() {
        data.emplace_back();
    }

    bool isRoot(BDDNode& node) {
        return &node == data.data();
    }

    bool isLeaf(BDDNode& node) {
        return node.constraintID != ConstraintId::undef();
    }

    bool isEmpty(BDDNode& node) {
        assert(node.left != 0 || node.right == 0);
        return node.left == 0 && node.constraintID == ConstraintId::undef();
    }

    BDDNode& get(BDDNodeRef ref) {
        assert(0 <= ref && ref < data.size());
        return data[ref];
    }

    BDDNodeRef newNode(BDDNodeRef parent) {
        data.emplace_back();
        data.back().parent = parent;
        return data.size() - 1;
    }


    unordered_set<size_t> getQueried(BDDNode& node){
        unordered_set<size_t> result;

        if (isEmpty(node) && isRoot(node)) {
            return result;
        }

        if (!isEmpty(node)) {
            result.insert(node.var);
        }

        BDDNode* current = &node;
        while (!isRoot(*current)) {
            current = &get(current->parent);
            result.insert(current->var);
        }

        return result;
    }

    bool isOkToBeOpen(BDDNodeRef ref) {
        assert(isEmpty(get(ref)));

        size_t nVars = 0;
        bool rhs = false;
        while (!isRoot(get(ref))) {
            BDDNode& parent = get(get(ref).parent);
            // maybe the node is not open because we found a clause
            // that covers it after creation of the node
            if (isLeaf(parent)) {
                return true;
            }
            if (parent.left == ref) {
                rhs ^= true;
            }
            nVars += 1;
            ref = get(ref).parent;
        }

        stats.nOpen += 1;
        return (nVars == this->nVars) && (rhs == this->rhs);
    }

    bool isHappy() {
        stats.nOpen = 0;
        for (BDDNodeRef ref = 0; ref < data.size(); ref++) {
            if (isEmpty(get(ref))) {
                if (!isOkToBeOpen(ref)) {
                    return false;
                }
            }
        }

        return true;
    }

    void addClause(Clause& clause) {
        constraintCounter += 1;
        map<size_t, bool> lits;
        for (auto l: clause) lits[l.var()] = l.sign();
        if (lits.size() == 1) return;

        vector<BDDNodeRef> open;
        open.push_back(0);

        while (open.size() != 0) {
            BDDNodeRef current = open.back();
            open.pop_back();

            BDDNode& node = get(current);

            if (isEmpty(node)) {
                auto queried = getQueried(node);

                auto it = lits.begin();
                for (; it != lits.end(); ++it) {
                    size_t var = it->first;
                    if (queried.find(var) == queried.end()) {
                        break;
                    }
                }

                if (it == lits.end()) {
                    node.constraintID = clause.stats.ID;
                } else {
                    BDDNodeRef left = newNode(current);
                    BDDNodeRef right = newNode(current);
                    // get new reference as newNode might invalidate previous reference
                    BDDNode& node = get(current);
                    node.var = it->first;
                    node.left = left;
                    node.right = right;
                    bool isNegated = it->second;
                    if (isNegated) {
                        open.push_back(node.left);
                    } else {
                        open.push_back(node.right);
                    }
                }
            } else if (!isLeaf(node)) {
                size_t var = node.var;
                auto it = lits.find(var);
                if (it == lits.end()) {
                    auto queried = getQueried(node);
                    bool isClosingNode = true;
                    for (auto pair: lits) {
                        size_t var = pair.first;
                        auto it = queried.find(var);
                        if (it == queried.end()) {
                            isClosingNode = false;
                            break;
                        }
                    }
                    if (isClosingNode) {
                        node.constraintID = clause.stats.ID;
                    } else {
                        open.push_back(node.left);
                        open.push_back(node.right);
                    }
                } else {
                    bool isNegated = it->second;
                    if (isNegated) {
                        open.push_back(node.left);
                    } else {
                        open.push_back(node.right);
                    }
                }
            }
        }
    }


    void addDotNodeStyle(ostream &out, BDDNode& node, size_t idx) {
        out << "  " << idx << " [label=\"";
        if (isLeaf(node)) {
            out << "c" << node.constraintID;
        } else if (isEmpty(node)) {
            out << "empty";
        } else {
            out << node.var;
        }
        out << "\"";

        if (isEmpty(node)) {
            if (isOkToBeOpen(idx)) {
                out << ",color=green,style=filled";
            } else {
                out << ",color=red,style=filled";
            }
        }

        out << "];\n";
    }


    void toDOT(ostream &out){
        out << "digraph G { \n";
        for (size_t i = 0; i < data.size(); i++) {
            BDDNode& node = get(i);
            addDotNodeStyle(out, node, i);

            if (!isLeaf(node) && !isEmpty(node)) {
                out << "  " << i << " -> " << node.left << " [label=\"t\"];\n";
                out << "  " << i << " -> " << node.right << " [label=\"f\"];\n";
            }
        }
        out << "}";
    }
};

