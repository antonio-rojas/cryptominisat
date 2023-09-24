#pragma once

#include <fstream>
#include <iostream>
#include <cstdio>
#include <cstring>
#include <string>
#include <unordered_set>

static uint16_t const strHex[16] = {'0', '1', '2', '3', '4', '5', '6',
'7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};

inline size_t itoa_hex(char *dst, uint64_t val)
{
    uint64_t mask = 0xFull;
    uint64_t val2 = val;
    char *p = dst;
    while (val2 != 0) {
        p += 1;
        val2 >>= 4;
    }

    size_t len = p - dst;

    while (val != 0) {
        p -= 1;
        *p = strHex[val & mask];
        val >>= 4;
    }

    return len;
}

// Based on
// https://stackoverflow.com/questions/7890194/optimized-itoa-function

class alignas(256) Digits {
private:
    uint16_t digits[100];
    Digits() {
        const char* const str =
            "00" "01" "02" "03" "04" "05" "06" "07" "08" "09"
            "10" "11" "12" "13" "14" "15" "16" "17" "18" "19"
            "20" "21" "22" "23" "24" "25" "26" "27" "28" "29"
            "30" "31" "32" "33" "34" "35" "36" "37" "38" "39"
            "40" "41" "42" "43" "44" "45" "46" "47" "48" "49"
            "50" "51" "52" "53" "54" "55" "56" "57" "58" "59"
            "60" "61" "62" "63" "64" "65" "66" "67" "68" "69"
            "70" "71" "72" "73" "74" "75" "76" "77" "78" "79"
            "80" "81" "82" "83" "84" "85" "86" "87" "88" "89"
            "90" "91" "92" "93" "94" "95" "96" "97" "98" "99";

        char* ptr = reinterpret_cast<char*>(digits);
        memcpy(ptr, str, 100 * sizeof(uint16_t));
    }
public:
    static const uint16_t* get() {
        static Digits digits;
        return digits.digits;
    }

};

inline size_t itoa_dump(char *dst, uint64_t val)
{
    uint16_t v = val;
    memcpy(dst, &v, sizeof(uint16_t));
    return 2;
}

inline size_t itoa(char *dst, uint64_t val)
{
    char buf[20];
    char *p = &buf[20];

    const uint16_t* digits = Digits::get();

    while(val >= 100)
    {
        p -= 2;
        memcpy(p, &digits[val % 100], sizeof(uint16_t));
        val /= 100;
    }

    p -= 2;
    memcpy(p, &digits[val], sizeof(uint16_t));

    p += val < 10;
    size_t len = buf - p + 20;
    memcpy(dst, p, len);
    return len;
}

class FastStream;

/**
 * When exit(.) is called the stack is not unwinded and destructors
 * are not guaranteed to be called. However, static objects will be
 * destructed (see https://en.cppreference.com/w/cpp/utility/program/exit).
 * This is a static (Singleton) that keeps track of open streams and
 * closes them on exit.
 *
 * This will also work properly for static FastStreams because
 * destructors will be called in reverse order of completion of the
 * constructor.
 */
class FastStreamFlushOnExitHandler {
private:
    std::unordered_set<FastStream*> handledFiles;

    FastStreamFlushOnExitHandler(){}

    ~FastStreamFlushOnExitHandler();
public:
    static FastStreamFlushOnExitHandler& get() {
        static FastStreamFlushOnExitHandler handler;
        return handler;
    }

    void add(FastStream* file) {
        handledFiles.insert(file);
    }

    void remove(FastStream* file) {
        handledFiles.erase(file);
    }
};

class FastStream {
    static const size_t bufferSize = 1*1024*1024;
    char buffer[bufferSize];
    char* used = buffer;
    char* end = buffer + bufferSize;
    FILE* file;

private:
    void flush() {
        fwrite(buffer , sizeof(char), used - buffer, file);
        fflush(file);
        used = buffer;
    }

    void checked_flush() {
        if (end - used < 1024) {
            flush();
        }
    }

public:
    FastStream(std::string filename, bool flushOnExit = true) {
        file = fopen(filename.c_str(),"w");
        if (setvbuf(file, NULL, _IONBF, 0) < 0) {
            // todo: add proper error reporting via exceptions.
            throw "Error while setting buffer.";
        }

        if (flushOnExit) {
            FastStreamFlushOnExitHandler::get().add(this);
        }
    }

    ~FastStream() {
        if (file != nullptr) {
            flush();
            fclose(file);
            FastStreamFlushOnExitHandler::get().remove(this);
            file = nullptr;
        }
    }

    FastStream& operator<<(const uint64_t& what) {
        used += itoa(used, what);
        checked_flush();
        return *this;
    }

    FastStream& operator<<(const int64_t& what) {
        assert(what > 0 && "Negative integers currently not supported!");
        return (*this) << static_cast<uint64_t>(what);
    }

    FastStream& operator<<(const uint32_t& what) {
        used += itoa(used, what);
        checked_flush();
        return *this;
    }

    FastStream& operator<<(const int32_t& what) {
        assert(what > 0 && "Negative integers currently not supported!");
        return (*this) << static_cast<uint32_t>(what);
    }

    FastStream& operator<<(const char* what) {
        size_t len = strlen(what);
        memcpy(used, what, len);
        used += len;
        checked_flush();
        return *this;
    }

    FastStream& put(const char what) {
        *used = what;
        used += 1;
        checked_flush();
        return *this;
    }

    FastStream& operator<<(const std::string& what) {
        return *this << what.c_str();
    }
};

inline FastStreamFlushOnExitHandler::~FastStreamFlushOnExitHandler(){
    std::vector<FastStream*> toDelete;
    std::copy(handledFiles.begin(), handledFiles.end(), std::back_inserter(toDelete));

    for (FastStream* f: toDelete) {
        if (f != nullptr) {
            f->~FastStream();
        }
    }
}