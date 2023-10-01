#pragma once

#include <vector>
#include "prooflogging/pbp/pbp_proof.hpp"
#include "prooflogging/ConstraintId.hpp"
#include "xor.h"
#include "prooflogging/bdd.hpp"

namespace pbp {
    class XorHandle {
    public:
        ConstraintId a;
        ConstraintId b;
    };

    XorHandle newXorHandleFromProofTree(
        Proof& proof,
        Xor& xr,
        BDD& proofTree);

    XorHandle xorFromEquality(ConstraintId a, ConstraintId b);

    XorHandle xorSum(
        Proof& proof,
        const std::vector<XorHandle>& v);

    ConstraintId reasonGeneration(
        Proof& proof,
        const XorHandle& xr,
        const std::vector<Lit>& reasonClause);

    void deleteXor(Proof& proof, const XorHandle& xr);
}
