#include <cassert>
#include <map>
#include <utility>
#include <unordered_set>

#include "prooflogging/bdd.hpp"
#include "pbp_xor_proof.hpp"
#include "prooflogging/pbp/pbp_proof.hpp"
#include "xor.h"
#include "clause.h"

#include "solvertypesmini.h"

using std::make_pair;
using std::vector;
using std::unordered_set;
using std::map;
using std::ostream;

namespace pbp { namespace xr {}}


vector<Lit> number2clause(const std::vector<uint32_t>& vars, uint32_t number) {
    std::vector<Lit> result(vars.size());
    uint32_t mask = 1;
    for (size_t i = 0; i < vars.size(); i++) {
        size_t j = vars.size() - 1 - i;
        Lit lit = Lit(vars[j], false);
        if ((mask & number) == 0) {
            result[j] = lit;
        } else {
            result[j] = ~lit;
        }
        mask = mask << 1;
    }
    assert((number & ~(mask - 1)) == 0);
    return result;
}


class FullAdder {
private:
    // could be int8_t but then we would need to fix printing
    typedef int16_t CoeffTypeLitDef;

public:
    Lit y;
    Lit z;

    ConstraintId geq;
    ConstraintId leq;

    FullAdder(pbp::Proof& proof, Lit x1, Lit x2):
        y(Lit(proof.newVar(), false)),
        z(Lit(proof.newVar(), false))
    {
        assert(x1 != x2);
        pbp::LiteralDefinition<CoeffTypeLitDef> defY(proof, y, {1,1}, {x1, x2}, 2);
        pbp::LiteralDefinition<CoeffTypeLitDef> defZ(proof, z, {1, 1, -2}, {x1, x2, y}, 1);
        logEquality(proof, defY, defZ);
    }

    FullAdder(pbp::Proof& proof, Lit x1, Lit x2, Lit x3):
        y(Lit(proof.newVar(), false)),
        z(Lit(proof.newVar(), false))

    {
        assert(x1 != x2);
        assert(x2 != x3);
        assert(x1 != x3);
        pbp::LiteralDefinition<CoeffTypeLitDef> defY(proof, y, {1, 1, 1}, {x1, x2, x3}, 2);
        pbp::LiteralDefinition<CoeffTypeLitDef> defZ(proof, z, {1, 1, 1, -2}, {x1, x2, x3, y}, 1);
        logEquality(proof,defY, defZ);
    }

    void logEquality(pbp::Proof& proof,
            pbp::LiteralDefinition<CoeffTypeLitDef>& defY,
            pbp::LiteralDefinition<CoeffTypeLitDef>& defZ) {
        {
            pbp::PolishNotationStep stepGeq(proof);
            stepGeq.append(defZ.rightImpl);
            stepGeq.append(defY.rightImpl).multiply(2).add();
            stepGeq.floor_div(3);
            geq = stepGeq.id;
        }

        {
            pbp::PolishNotationStep stepLeq(proof);
            stepLeq.append(defZ.leftImpl);
            stepLeq.append(defY.leftImpl).multiply(2).add();
            stepLeq.floor_div(3);
            leq = stepLeq.id;
        }
    }
};

pbp::xr::XorHandle pbp::xr::xorFromEquality(ConstraintId a, ConstraintId b) {
    return XorHandle{a,b};
}

pbp::xr::XorHandle pbp::xr::xorSum(pbp::Proof& proof, const vector<pbp::xr::XorHandle>& v) {
    assert(v.size() > 0);
    XorHandle result;

    {
        PolishNotationStep step(proof);
        auto it = v.begin();
        step.append(it->a);
        it++;
        for (; it != v.end(); ++it) {
            step.append(it->a).add();
        }
        result.a = step.id;
    }

    {
        PolishNotationStep step(proof);
        auto it = v.begin();
        step.append(it->b);
        it++;
        for (; it != v.end(); ++it) {
            step.append(it->b).add();
        }
        result.b = step.id;
    }

    return result;
}

void reasonGeneration(pbp::PolishNotationStep& step, const pbp::xr::XorHandle& xr, const vector<Lit>& clause) {
    step.append(xr.a);
    for (auto lit: clause) {
        step.appendLit(lit).add();
    }
    step.floor_div(2).multiply(2).append(xr.b).add();
}

ConstraintId pbp::xr::reasonGeneration(
        Proof& proof, const XorHandle& xr, const vector<Lit>& clause) {
    ConstraintId result;
    {
        PolishNotationStep step(proof);
        ::reasonGeneration(step, xr, clause);
        result = step.id;
    }

    #if !defined(NDEBUG)
    {
        EqualityCheck check(proof, result);
        for (auto lit: clause) {
            check.addTerm(1, lit);
        }
        check.setDegree(1);
    }
    #endif

    return result;
}

class XORFromClauses {
private:
    pbp::Proof& proof;
    Xor& xr;

    struct XorWithFreeParity {
        pbp::xr::XorHandle id;
        Lit parityLit = lit_Undef;
    };

    XorWithFreeParity xorWithFreeParity() {
        #if !defined(NDEBUG)
            proof << "* derive xor with free parity\n";
        #endif
        assert(xr.vars.size() > 1);

        XorWithFreeParity result;

        vector<FullAdder> adderChain;

        auto it = xr.vars.rbegin();
        if (xr.vars.size() % 2 == 0) {
            assert(xr.vars.size() >= 2);
            Lit x1 = Lit(*it, false);
            Lit x2 = Lit(*(++it), xr.rhs);
            adderChain.emplace_back(proof, x1, x2);
        } else {
            assert(xr.vars.size() >= 3);
            Lit x1 = Lit(*it, false);
            Lit x2 = Lit(*(++it), false);
            Lit x3 = Lit(*(++it), xr.rhs);
            adderChain.emplace_back(proof, x1, x2, x3);
        }

        while (++it != xr.vars.rend()) {
            Lit x1 = Lit(*it, false);
            Lit x2 = Lit(*(++it), false);
            adderChain.emplace_back(proof, adderChain.back().z, x1, x2);
        }

        result.parityLit = adderChain.back().z;

        // Geq
        {
            pbp::PolishNotationStep stepGeq(proof);

            auto adderIt = adderChain.begin();
            stepGeq.append(adderIt->geq);
            ++adderIt;
            for (;adderIt != adderChain.end(); adderIt++) {
                stepGeq.append(adderIt->geq).add();
            }

            result.id.a = stepGeq.id;
        }

        // Leq
        {
            pbp::PolishNotationStep stepLeq(proof);

            auto adderIt = adderChain.begin();
            stepLeq.append(adderIt->leq);
            ++adderIt;
            for (;adderIt != adderChain.end(); adderIt++) {
                stepLeq.append(adderIt->leq).add();
            }
            result.id.b = stepLeq.id;
        }

        return result;
    }

    pbp::xr::XorHandle fixParity(const XorWithFreeParity& fp, ConstraintId unitParityLit) {
        #if !defined(NDEBUG)
            proof << "* fix of xor with free parity\n";
        #endif
        pbp::xr::XorHandle result;
        {
            pbp::PolishNotationStep step(proof);
            step.append(fp.id.a);
            if (xr.rhs) {
                step.appendLit(~fp.parityLit);
            } else {
                step.appendLit(unitParityLit);
            }
            step.add();
            result.a = step.id;
        }

        {
            pbp::PolishNotationStep step(proof);
            step.append(fp.id.b);
            if (!xr.rhs) {
                step.appendLit(fp.parityLit);
            } else {
                step.appendLit(unitParityLit);
            }
            step.add();
            result.b = step.id;
        }
        return result;
    }

    ConstraintId unitFromOrderedClauses(
        const XorWithFreeParity& fp,
        const vector<ConstraintId>& constraints
    ) {
        assert(constraints.size() == (1ul << (xr.vars.size() - 1)));

        Lit parityLit(fp.parityLit);
        if (xr.rhs == true) {
            parityLit = ~parityLit;
        }

        size_t maxFlipBit = 0;
        pbp::PolishNotationStep step(proof);
        for (size_t i = 0; i < constraints.size(); i++) {
            uint32_t assignment = (i << 1);
            cout << __builtin_popcount(assignment) << endl;
            assignment += __builtin_popcount(assignment) ^ !xr.rhs;
            vector<Lit> clause = number2clause(xr.vars, assignment);
            clause.push_back(parityLit);

            reasonGeneration(step, fp.id, clause);

            if (i == 0) {
                step.split();
            }

            step.append(constraints[i]);
            step.add().saturate();

            if (i == 0) {
                step.split();
            }

            uint32_t flipToZero = i & (i ^ (i+1));
            for (size_t bit = 0; bit < xr.vars.size() - 1; bit += 1) {
                if (flipToZero & (1 << bit)) {
                    step.add().saturate();
                    if (bit == maxFlipBit) {
                        maxFlipBit += 1;
                        step.split();
                    }
                }
            }
        }

        return step.id;
    }

    struct DFSInfo {
        bool finished = false;
        BDDNodeRef ref;
        DFSInfo(BDDNodeRef ref):ref(ref){}
    };

    ConstraintId unitFromProofTree(
        const XorWithFreeParity& fp,
        BDD& bdd
    ){
        #if !defined(NDEBUG)
            proof << "* derive unit clause of parity literal\n";
        #endif
        pbp::PolishNotationStep step(proof);

        vector<DFSInfo> open;
        open.emplace_back(0);

        while (open.size() != 0) {
            DFSInfo& info = open.back();
            if (info.finished) {
                step.add().saturate();

                BDDNodeRef ref = info.ref;
                open.pop_back();

                while (!bdd.isRoot(bdd.get(ref))) {
                    BDDNode& parent = bdd.get(bdd.get(ref).parent);
                    if (parent.left != ref) {
                        goto no_split;
                    }
                    ref = bdd.get(ref).parent;
                }

                step.split();
                no_split:
                continue;
            } else {
                info.finished = true;
                BDDNodeRef current = info.ref;
                BDDNode& node = bdd.get(current);

                if (!bdd.isEmpty(node) && !bdd.isLeaf(node)) {
                    open.emplace_back(node.right);
                    open.emplace_back(node.left);
                } else {
                    open.pop_back();

                    vector<Lit> clause;

                    BDDNodeRef ref = current;
                    bool parity = false;
                    while (!bdd.isRoot(bdd.get(ref))) {
                        BDDNode& parent = bdd.get(bdd.get(ref).parent);
                        Lit lit = Lit(parent.var, false);
                        if (parent.left == ref) {
                            lit = ~lit;
                            parity ^= true;
                        }

                        clause.push_back(lit);
                        ref = bdd.get(ref).parent;
                    }

                    if (bdd.isEmpty(node)) {
                        if (parity) {
                            clause.push_back(fp.parityLit);
                        } else {
                            clause.push_back(~fp.parityLit);
                        }
                        reasonGeneration(step, fp.id, clause);
                    } else {
                        assert(bdd.isLeaf(node));
                        step.append(node.constraintID);

                        // // we might only have a subclause, make sure
                        // // we have a full clause
                        // for (Lit lit:clause) {
                        //     step.append(lit).add();
                        // }
                        // step.saturate();
                    }
                }
            }
        }

        return step.id;
    }

public:
    XORFromClauses(
        pbp::Proof& _proof,
        Xor& _xr
    )
        : proof(_proof)
        , xr(_xr)
    {
        vector<uint32_t>& v = xr.vars;
        sort(v.begin(), v.end(), [ ]( const auto& lhs, const auto& rhs )
        {
            return lhs < rhs;
        });
        auto it = adjacent_find(v.begin(), v.end());
        // for (auto lit: xr.lits) {
        //     LOG(debug) << lit << " ";
        // }
        // LOG(debug) << EOM;
        if (it != v.end()) LOG(fatal) << "found dulicate!" << EOM;
    }

    void checkUnit(const XorWithFreeParity& fp, ConstraintId id) {
        Lit parityLit(fp.parityLit);
        if (xr.rhs != true) {
            parityLit = ~parityLit;
        }
        pbp::EqualityCheck check(proof, id);
        check.addTerm(1, parityLit);
        check.setDegree(1);
    }

    void checkXor(ConstraintId) {
        //todo?
    }

    /*
     * the constraints need to be sorted such that, w.r.t, the
     * variable order provided by vars clauses that contain a
     * literal unnegated apear before claues where the literal is
     * negated
     */
    pbp::xr::XorHandle fromOrderdClauses(const vector<ConstraintId>& constraints) {
        auto fp = xorWithFreeParity();
        auto unit = unitFromOrderedClauses(fp, constraints);
        return fixParity(fp, unit);
    }

    pbp::xr::XorHandle fromProofTree(BDD& tree) {
        auto fp = xorWithFreeParity();
        auto unit = unitFromProofTree(fp, tree);
#ifndef NDEBUG
        checkUnit(fp, unit);
#endif
        return fixParity(fp, unit);
    }

};

pbp::xr::XorHandle pbp::xr::newXorHandleFromProofTree(pbp::Proof& proof, Xor& xr, BDD& proofTree) {
    XORFromClauses helper(proof, xr);
    return helper.fromProofTree(proofTree);
}

void pbp::xr::deleteXor(pbp::Proof& proof, const XorHandle& xr) {
    DeleteStep step(proof);
    step.addDeletion(xr.a);
    step.addDeletion(xr.b);
}
