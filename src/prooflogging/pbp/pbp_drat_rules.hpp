#pragma once

#include "prooflogging/ConstraintId.hpp"
#include "prooflogging/pbp/pbp_proof.hpp"
#include "solvertypesmini.h"

using namespace CMSat;

namespace proof {
namespace pbp {
namespace drat_rules {
    template<typename T>
    ConstraintId add(Proof& proof, T begin, T end) {
        PBPRStep step(proof);
        for (auto it = begin; it != end; ++it) {
            step.template addTerm<int>(1, *it);
        }
        step.setDegree(1);
        return step.id;
    }

    template<typename T>
    ConstraintId add(Proof& proof, T dat) {
        return add(proof, dat.begin(), dat.end());
    }

    template<typename T>
    ConstraintId add(Proof& proof, Lit a) {
        PBPRStep step(proof);
        step.template addTerm<int>(1, a);
        step.setDegree(1);
        return step.id;
    }

    template<typename T>
    ConstraintId add2(Proof& proof, T a, T b) {
        PBPRStep step(proof);
        step.template addTerm<int>(1, a);
        step.template addTerm<int>(1, b);
        step.setDegree(1);
        return step.id;
    }

    template<typename T>
    void del(Proof& proof, ConstraintId id, T begin, T end) {
        #if !defined(NDEBUG)
            EqualityCheck check(proof, id);
            for (T it = begin; it != end; ++it) {
                check.addTerm(1, *it);
            }
            check.setDegree(1);
        #endif

        DeleteStep del(proof);
        del.addDeletion(id);
    }
    template<typename T>
    void del(Proof& proof, ConstraintId id, T dat) {
        del(proof, id, dat.begin(), dat.end());
    }

    inline ConstraintId contradiction(Proof& proof) {
        Lit* l = nullptr;
        ConstraintId result = add(proof, l, l);
        ContradictionStep step(proof, result);
        return result;
    }
}}}
