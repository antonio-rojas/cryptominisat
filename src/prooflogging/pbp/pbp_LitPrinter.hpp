#include <iostream>
#include "prooflogging/LitName.hpp"
#include "prooflogging/FastStream.hpp"
#include <cstdint>

namespace proof {
namespace pbp {
    class LitPrinter {
    public:
        LitName name;
        LitPrinter(LitName _name) : name(_name) {}
    };

    inline FastStream& operator<<(FastStream& out, const LitPrinter& printer) {
        int64_t lit = printer.name.lit;
        if (lit < 0) {
            out << "~";
            lit *= -1;
        }
        if (printer.name.text != nullptr) {
            out << printer.name.text;
        } else {
            out << "x";
            out << static_cast<uint64_t>(lit);
        }
        return out;
    }

    inline std::ostream& operator<<(std::ostream& out, const LitPrinter& printer) {
        int64_t lit = printer.name.lit;
        if (lit < 0) {
            out << "~";
            lit *= -1;
        }
        if (printer.name.text != nullptr) {
            out << printer.name.text;
        } else {
            out << "x";
            out << static_cast<uint64_t>(lit);
        }
        return out;
    }
}
}
