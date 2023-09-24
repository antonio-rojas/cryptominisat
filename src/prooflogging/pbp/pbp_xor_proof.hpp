#pragma once

#include <vector>
#include "prooflogging/Proof.hpp"
#include "prooflogging/ConstraintId.hpp"

namespace xorp {
    template<typename Types>
    struct Xor;
    class BDD;
}


namespace proof {
    namespace pbp {
        namespace xr {
            template<typename Types>
            class XorHandle {
            public:
                ConstraintId a;
                ConstraintId b;
            };

            template<typename Types>
            XorHandle<Types> newXorHandleFromProofTree(
                pbp::Proof<Types>& proof,
                xorp::Xor<Types>& xr,
                xorp::BDD& proofTree);

            template<typename Types>
            XorHandle<Types> xorFromEquality(ConstraintId a, ConstraintId b);

            template<typename Types>
            XorHandle<Types> xorSum(
                pbp::Proof<Types>& proof,
                const std::vector<XorHandle<Types>>& v);

            template<typename Types>
            ConstraintId reasonGeneration(
                pbp::Proof<Types>& proof,
                const XorHandle<Types>& xr,
                const std::vector<typename Types::Lit>& reasonClause);

            template<typename Types>
            void deleteXor(
                pbp::Proof<Types>& proof,
                const XorHandle<Types>& xr);
        }
    }
}
