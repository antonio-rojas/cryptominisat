#pragma once

#include <iostream>
#include <cstdint>

class ConstraintId {
public:
    uint32_t id;
    explicit ConstraintId (uint32_t _id) : id(_id) {}

    ConstraintId () : id(0) {}
    static ConstraintId undef() {
        return ConstraintId{0};
    }

    bool operator==(ConstraintId other) {
        return other.id == id;
    }

    bool operator!=(ConstraintId other) {
        return !(*this == other);
    }

    friend std::ostream& operator<< (std::ostream &out, const ConstraintId &node);
};

inline std::ostream& operator<< (std::ostream &out, const ConstraintId &node) {
    return out << node.id;
}
