#pragma once

#include <cstdint>

class LitName {
public:
    int64_t lit;
    const char * text;

    LitName(int64_t _lit)
        : lit(_lit)
        , text(nullptr)
    {}

    LitName(const char * text, bool isNegated = false)
        : lit(isNegated ? -1 : 1)
        , text(text)
    {}
};
