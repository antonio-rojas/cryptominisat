#include "pbp_xor_proof.hpp"
#include "pbp_proof.hpp"
/* #include "xorengine/private/myXor.hpp" */
#include "xorengine/XorDetector.ipp"
#include "prooflogging/xor_2_clauses.hpp"
#include "solvertypesmini.h"

using namespace proof::pbp;
using namespace proof::pbp::xr;
using namespace xorp;

class FullAdder {
private:
    // could be int8_t but then we would need to fix printing
    typedef int16_t CoeffTypeLitDef;

public:
    Lit y;
    Lit z;

    proof::ConstraintId geq;
    proof::ConstraintId leq;

    FullAdder(Proof& proof, Lit x1, Lit x2):
        y(Lit(proof.newVar(), false)),
        z(Lit(proof.newVar(), false))
    {
        assert(x1 != x2);
        LiteralDefinition<CoeffTypeLitDef> defY(proof, y, {1,1}, {x1, x2}, 2);
        LiteralDefinition<CoeffTypeLitDef> defZ(proof, z, {1, 1, -2}, {x1, x2, y}, 1);
        logEquality(proof, defY, defZ);
    }

    FullAdder(Proof& proof, Lit x1, Lit x2, Lit x3):
        y(Lit(proof.newVar(), false)),
        z(Lit(proof.newVar(), false))

    {
        assert(x1 != x2);
        assert(x2 != x3);
        assert(x1 != x3);
        LiteralDefinition<CoeffTypeLitDef> defY(proof, y, {1, 1, 1}, {x1, x2, x3}, 2);
        LiteralDefinition<CoeffTypeLitDef> defZ(proof, z, {1, 1, 1, -2}, {x1, x2, x3, y}, 1);
        logEquality(proof,defY, defZ);
    }

    void logEquality(Proof& proof,
            LiteralDefinition<CoeffTypeLitDef>& defY, LiteralDefinition<CoeffTypeLitDef>& defZ) {
        {
            PolishNotationStep stepGeq(proof);
            stepGeq.append(defZ.rightImpl);
            stepGeq.append(defY.rightImpl).multiply(2).add();
            stepGeq.floor_div(3);
            geq = stepGeq.id;
        }

        {
            PolishNotationStep stepLeq(proof);
            stepLeq.append(defZ.leftImpl);
            stepLeq.append(defY.leftImpl).multiply(2).add();
            stepLeq.floor_div(3);
            leq = stepLeq.id;
        }
    }
};

XorHandle proof::pbp::xr::xorFromEquality(proof::ConstraintId a, proof::ConstraintId b) {
    return XorHandle{a,b};
}

XorHandle proof::pbp::xr::xorSum(Proof& proof, const std::vector<XorHandle>& v) {
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

void reasonGeneration(PolishNotationStep& step, const XorHandle& xr, const std::vector<Lit>& clause) {
    step.append(xr.a);
    for (auto lit: clause) {
        step.appendLit(lit).add();
    }
    step.floor_div(2).multiply(2).append(xr.b).add();
}

proof::ConstraintId proof::pbp::xr::reasonGeneration(
        Proof& proof, const XorHandle& xr, const std::vector<Lit>& clause) {
    proof::ConstraintId result;
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
    Proof& proof;
    xorp::Xor& xr;

    struct XorWithFreeParity {
        XorHandle id;
        Lit parityLit = lit_Undef;
    };

    XorWithFreeParity xorWithFreeParity() {
        #if !defined(NDEBUG)
            proof << "* derive xor with free parity\n";
        #endif
        assert(xr.lits.size() > 1);

        XorWithFreeParity result;

        std::vector<FullAdder> adderChain;

        auto it = xr.lits.rbegin();
        if (xr.lits.size() % 2 == 0) {
            assert(xr.lits.size() >= 2);
            Lit x1 = *it;
            Lit x2 = *(++it);
            adderChain.emplace_back(proof, x1, x2);
        } else {
            assert(xr.lits.size() >= 3);
            Lit x1 = *it;
            Lit x2 = *(++it);
            Lit x3 = *(++it);
            adderChain.emplace_back(proof, x1, x2, x3);
        }
        while (++it != xr.lits.rend()) {
            Lit x1 = *it;
            Lit x2 = *(++it);
            adderChain.emplace_back(proof, adderChain.back().z, x1, x2);
        }

        result.parityLit = adderChain.back().z;

        {
            PolishNotationStep stepGeq(proof);

            auto adderIt = adderChain.begin();
            stepGeq.append(adderIt->geq);
            ++adderIt;
            for (;adderIt != adderChain.end(); adderIt++) {
                stepGeq.append(adderIt->geq).add();
            }

            result.id.a = stepGeq.id;
        }

        {
            PolishNotationStep stepLeq(proof);

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

    XorHandle fixParity(const XorWithFreeParity& fp, proof::ConstraintId unitParityLit) {
        #if !defined(NDEBUG)
            proof << "* fix of xor with free parity\n";
        #endif
        XorHandle result;
        {
            PolishNotationStep step(proof);
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
            PolishNotationStep step(proof);
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

    proof::ConstraintId unitFromOrderedClauses(
        const XorWithFreeParity& fp,
        const std::vector<proof::ConstraintId>& constraints
    ) {
        assert(constraints.size() == (1ul << (xr.lits.size() - 1)));

        Lit parityLit(fp.parityLit);
        if (xr.rhs == true) {
            parityLit = ~parityLit;
        }

        size_t maxFlipBit = 0;
        PolishNotationStep step(proof);
        for (size_t i = 0; i < constraints.size(); i++) {
            uint32_t assignment = (i << 1);
            std::cout << popCountMod2(assignment) << std::endl;
            assignment += popCountMod2(assignment) ^ !xr.rhs;
            std::vector<Lit> clause = number2clause(xr.lits, assignment);
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
            for (size_t bit = 0; bit < xr.lits.size() - 1; bit += 1) {
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

    proof::ConstraintId unitFromProofTree(
        const XorWithFreeParity& fp,
        xorp::BDD& bdd
    ){
        #if !defined(NDEBUG)
            proof << "* derive unit clause of parity literal\n";
        #endif
        PolishNotationStep step(proof);

        std::vector<DFSInfo> open;
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

                    std::vector<Lit> clause;

                    BDDNodeRef ref = current;
                    bool parity = false;
                    while (!bdd.isRoot(bdd.get(ref))) {
                        BDDNode& parent = bdd.get(bdd.get(ref).parent);
                        Lit lit = variable::toLit<Lit>(parent.var);
                        if (parent.left == ref) {
                            lit = literal::negated(lit);
                            parity ^= true;
                        }


                        clause.push_back(lit);
                        ref = bdd.get(ref).parent;
                    }

                    if (bdd.isEmpty(node)) {
                        if (parity) {
                            clause.push_back(fp.parityLit);
                        } else {
                            clause.push_back(literal::negated(fp.parityLit));
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
        Proof& _proof,
        xorp::Xor& _xr
    )
        : proof(_proof)
        , xr(_xr)
    {
        std::vector<Lit>& v = xr.lits;
        std::sort(v.begin(), v.end(), [ ]( const auto& lhs, const auto& rhs )
        {
            return xorp::literal::lessThan(lhs, rhs);
        });
        auto it = std::adjacent_find(v.begin(), v.end());
        // for (auto lit: xr.lits) {
        //     LOG(debug) << lit << " ";
        // }
        // LOG(debug) << EOM;
        if (it != v.end()) {
            LOG(fatal) << "found dulicate!" << EOM;
        }
    }

    void checkUnit(const XorWithFreeParity& fp, proof::ConstraintId id) {
        Lit parityLit(fp.parityLit);
        if (xr.rhs != true) {
            parityLit = ~parityLit;
        }
        proof::pbp::EqualityCheck check(proof, id);
        check.addTerm(1, parityLit);
        check.setDegree(1);
    }

    void checkXor(proof::ConstraintId) {
        //todo?
    }

    /*
     * the constraints need to be sorted such that, w.r.t, the
     * variable order provided by vars clauses that contain a
     * literal unnegated apear before claues where the literal is
     * negated
     */
    XorHandle fromOrderdClauses(const std::vector<proof::ConstraintId>& constraints) {
        auto fp = xorWithFreeParity();
        auto unit = unitFromOrderedClauses(fp, constraints);
        return fixParity(fp, unit);
    }

    XorHandle fromProofTree(xorp::BDD& tree) {
        auto fp = xorWithFreeParity();
        auto unit = unitFromProofTree(fp, tree);
        #if !defined(NDEBUG)
            checkUnit(fp, unit);
        #endif
        return fixParity(fp, unit);
    }

};

template<typename Types>
XorHandle proof::pbp::xr::newXorHandleFromProofTree(proof::pbp::Proof& proof, xorp::Xor& xr, xorp::BDD& proofTree) {
    XORFromClauses helper(proof, xr);
    return helper.fromProofTree(proofTree);
}

template<typename Types>
void proof::pbp::xr::deleteXor(proof::pbp::Proof& proof, const XorHandle& xr) {
    DeleteStep step(proof);
    step.addDeletion(xr.a);
    step.addDeletion(xr.b);
}
