#pragma once
#include "xorengine/private/assert.hpp"
#include "xorengine/SolverAdapter.hpp"


/*
 * Think of number as an assignment to the variables. If
 * number is 0 in the i-th bit from the left then the i-th
 * variable is false. The returned clause is falsified by the
 * assignment represented by number.
 */
template<typename Types>
std::vector<typename Types::Lit> number2clause(const std::vector<typename Types::Var>& vars, uint32_t number) {
    std::vector<typename Types::Lit> result(vars.size());
    uint32_t mask = 1;
    for (size_t i = 0; i < vars.size(); i++) {
        size_t j = vars.size() - 1 - i;
        typename Types::Lit lit = xorp::variable::toLit<typename Types::Lit>(vars[j]);
        if ((mask & number) == 0) {
            result[j] = lit;
        } else {
            result[j] = xorp::literal::negated(lit);
        }
        mask = mask << 1;
    }
    assert((number & ~(mask - 1)) == 0);
    return result;
}

template<typename T>
bool popCountMod2(T number) {
    uint remainingSize = sizeof(T) * 8;
    while (remainingSize != 1) {
        assert(remainingSize % 2 == 0);

        remainingSize = remainingSize / 2;
        number ^= (number >> remainingSize);
    }
    return number & 1;
}

template<typename Lit>
using AddXorCallbackIt = typename std::vector<Lit>::iterator;

template<typename Lit>
using AddXorCallback = std::function<void(AddXorCallbackIt<Lit>,AddXorCallbackIt<Lit>)>;