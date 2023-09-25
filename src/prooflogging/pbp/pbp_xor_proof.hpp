#pragma once

#include <vector>
#include "prooflogging/pbp/pbp_proof.hpp"
#include "prooflogging/ConstraintId.hpp"

namespace xorp {
    struct Xor;
    class BDD;
}

namespace proof {
    namespace pbp {
        namespace xr {
            class XorHandle {
            public:
                ConstraintId a;
                ConstraintId b;
            };

            XorHandle newXorHandleFromProofTree(
                pbp::Proof& proof,
                xorp::Xor& xr,
                xorp::BDD& proofTree);

            XorHandle xorFromEquality(ConstraintId a, ConstraintId b);

            XorHandle xorSum(
                pbp::Proof& proof,
                const std::vector<XorHandle>& v);

            ConstraintId reasonGeneration(
                pbp::Proof& proof,
                const XorHandle& xr,
                const std::vector<Lit>& reasonClause);

            void deleteXor(
                pbp::Proof& proof,
                const XorHandle& xr);
        }
    }
}
