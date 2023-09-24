#pragma once

#include "prooflogging/ConstraintId.hpp"
#include "prooflogging/pbp/pbp_proof.hpp"
#include "solvertypesmini.h"

using namespace CMSat;

namespace proof {
namespace pbp {
namespace drat_rules {
    template<typename Types, typename T>
    ConstraintId add(Proof<Types>& proof, T begin, T end) {
        PBPRStep<Types> step(proof);
        for (auto it = begin; it != end; ++it) {
            step.template addTerm<int>(1, *it);
        }
        step.setDegree(1);
        return step.id;
    }

    template<typename Types, typename T>
    ConstraintId add(Proof<Types>& proof, T dat) {
        return add(proof, dat.begin(), dat.end());
    }
    
    template<typename Types, typename T>
    ConstraintId add(Proof<Types>& proof, Lit a) {
        PBPRStep<Types> step(proof);
        step.template addTerm<int>(1, a);
        step.setDegree(1);
        return step.id;
    }

    template<typename Types, typename T>
    ConstraintId add2(Proof<Types>& proof, T a, T b) {
        PBPRStep<Types> step(proof);
        step.template addTerm<int>(1, a);
        step.template addTerm<int>(1, b);
        step.setDegree(1);
        return step.id;
    }

    template<typename Types, typename T>
    void del(Proof<Types>& proof, ConstraintId id, T begin, T end) {
        #if !defined(NDEBUG)
            EqualityCheck<Types> check(proof, id);
            for (T it = begin; it != end; ++it) {
                check.addTerm(1, *it);
            }
            check.setDegree(1);
        #endif

        DeleteStep<Types> del(proof);
        del.addDeletion(id);
    }
    template<typename Types, typename T>
    void del(Proof<Types>& proof, ConstraintId id, T dat) {
        del(proof, id, dat.begin(), dat.end());
    }

    template<typename Types>
    ConstraintId contradiction(Proof<Types>& proof) {
        typename Types::Lit* l = nullptr;
        ConstraintId result = add(proof, l, l);
        ContradictionStep<Types> step(proof, result);
        return result;
    }
}}}
