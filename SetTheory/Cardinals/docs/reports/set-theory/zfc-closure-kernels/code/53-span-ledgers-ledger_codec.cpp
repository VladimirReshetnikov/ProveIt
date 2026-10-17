// Lossless streaming codec for the DFS TSV ledgers in this research archive.
// Compile: c++ -O3 -std=c++17 ledger_codec.cpp -lz -lcrypto -o ledger_codec
// The Python front end compiles and invokes this helper automatically.
#include <array>
#include <charconv>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>
#include <openssl/evp.h>
#include <zlib.h>

using U64 = uint64_t;
using Big = unsigned __int128;
using Digest = std::array<unsigned char, 32>;
constexpr size_t BUFSIZE = 1 << 20;
constexpr int MAXDEGREE = 12;
constexpr char MAGIC[] = "PLEDG1\r\n";
const std::string HEADER2 = "group\tdeleted\ta0\ta1\toutcome\tcase_or_needed\treason\tweight\n";
const std::string HEADERN = "group\tdeleted\tassignments\toutcome\tcase_or_needed\treason\tweight\n";

[[noreturn]] void fail(const std::string &s) { throw std::runtime_error(s); }
void require(bool b, const std::string &s) { if (!b) fail(s); }
std::string hex(const Digest &d) {
    static const char *digits = "0123456789abcdef";
    std::string s; s.reserve(64);
    for (auto b : d) { s += digits[b >> 4]; s += digits[b & 15]; }
    return s;
}
struct Sha256 {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    Sha256() { require(ctx && EVP_DigestInit_ex(ctx, EVP_sha256(), nullptr) == 1, "SHA256 init failed"); }
    ~Sha256() { EVP_MD_CTX_free(ctx); }
    void update(const void *p, size_t n) { require(EVP_DigestUpdate(ctx, p, n) == 1, "SHA256 update failed"); }
    Digest finish() {
        Digest d{}; unsigned n;
        require(EVP_DigestFinal_ex(ctx, d.data(), &n) == 1 && n == 32, "SHA256 finish failed");
        return d;
    }
};
struct RawReader {
    FILE *file;
    std::vector<char> buf = std::vector<char>(BUFSIZE);
    size_t at = 0, end = 0;
    U64 bytes = 0;
    Sha256 sha;
    explicit RawReader(const char *name) : file(std::fopen(name, "rb")) { require(file, "cannot open raw ledger"); }
    ~RawReader() { std::fclose(file); }
    bool line(std::string &s) {
        s.clear();
        for (;;) {
            if (at == end) {
                end = std::fread(buf.data(), 1, buf.size(), file); at = 0;
                if (!end) {
                    require(!std::ferror(file), "raw ledger read failed");
                    require(s.empty(), "raw ledger is not newline terminated");
                    return false;
                }
                sha.update(buf.data(), end); bytes += end;
            }
            const char *start = buf.data() + at;
            const char *lf = static_cast<const char *>(std::memchr(start, '\n', end - at));
            size_t n = lf ? size_t(lf - start + 1) : end - at;
            s.append(start, n); at += n;
            require(s.size() <= 65536, "ledger line too long");
            if (lf) return true;
        }
    }
};
struct GzWriter {
    gzFile file;
    std::vector<unsigned char> buf;
    explicit GzWriter(const char *name) : file(gzopen(name, "wb9")) {
        require(file, "cannot open packed output"); gzbuffer(file, BUFSIZE); buf.reserve(BUFSIZE + 128);
    }
    ~GzWriter() { if (file) gzclose(file); }
    void flush() {
        if (buf.empty()) return;
        require(gzwrite(file, buf.data(), unsigned(buf.size())) == int(buf.size()), "packed output write failed");
        buf.clear();
    }
    void byte(unsigned char v) { buf.push_back(v); if (buf.size() >= BUFSIZE) flush(); }
    void data(const void *p, size_t n) {
        auto b = static_cast<const unsigned char *>(p);
        for (size_t i = 0; i < n; ++i) byte(b[i]);
    }
    void var(U64 n) { while (n >= 128) { byte((n & 127) | 128); n >>= 7; } byte(n); }
    void signedvar(int n) { var(n < 0 ? U64(-int64_t(n)) * 2 - 1 : U64(n) * 2); }
    void close() { flush(); int result = gzclose(file); file = nullptr; require(result == Z_OK, "packed output close failed"); }
};
struct GzReader {
    gzFile file;
    std::vector<unsigned char> buf = std::vector<unsigned char>(BUFSIZE);
    size_t at = 0, end = 0;
    explicit GzReader(const char *name) : file(gzopen(name, "rb")) {
        require(file, "cannot open packed ledger"); gzbuffer(file, BUFSIZE);
    }
    ~GzReader() { gzclose(file); }
    int optionalbyte() {
        if (at == end) {
            int n = gzread(file, buf.data(), unsigned(buf.size()));
            if (n <= 0) {
                int err; const char *s = gzerror(file, &err);
                require(n == 0 && (err == Z_OK || err == Z_STREAM_END), std::string("packed read failed: ") + s);
                return -1;
            }
            at = 0; end = size_t(n);
        }
        return buf[at++];
    }
    unsigned char byte() { int n = optionalbyte(); require(n >= 0, "truncated packed ledger"); return n; }
    void data(void *p, size_t n) { auto b = static_cast<unsigned char *>(p); for (size_t i = 0; i < n; ++i) b[i] = byte(); }
    U64 var() {
        U64 n = 0;
        for (int shift = 0; shift <= 63; shift += 7) {
            auto v = byte();
            require(shift < 63 || v <= 1, "oversized varint");
            n |= U64(v & 127) << shift;
            if (!(v & 128)) { require(shift == 0 || v != 0, "noncanonical varint"); return n; }
        }
        fail("oversized varint");
    }
    int integer() { U64 n = var(); require(n <= U64(INT32_MAX), "integer too large"); return int(n); }
    int signedvar() { U64 n = var(); require(n <= U64(INT32_MAX) * 2, "signed integer too large"); return (n & 1) ? -int(n / 2) - 1 : int(n / 2); }
};
int integer(std::string_view s) {
    int n = 0; auto r = std::from_chars(s.data(), s.data() + s.size(), n);
    require(r.ec == std::errc() && r.ptr == s.data() + s.size(), "invalid TSV integer");
    return n;
}
int split(std::string_view s, std::array<std::string_view, 8> &out) {
    int n = 0; size_t at = 0;
    for (;;) {
        size_t e = s.find('\t', at); require(n < int(out.size()), "too many TSV fields");
        out[n++] = s.substr(at, e == s.npos ? s.size() - at : e - at);
        if (e == s.npos) return n;
        at = e + 1;
    }
}
struct Event {
    int outcome = -1, value = 0, reason = 0;
    bool operator==(const Event &b) const { return outcome == b.outcome && value == b.value && reason == b.reason; }
};
void write_run(GzWriter &out, const Event &e, U64 count) {
    if (!count) return;
    out.byte(1); out.var(count); out.byte(e.outcome); out.signedvar(e.value); out.var(e.reason);
}

void pack(const char *raw, const char *packed, int choices) {
    require(choices >= 2 && choices <= 100000, "choices must be 2..100000");
    RawReader in(raw); GzWriter out(packed); std::string s;
    require(in.line(s), "empty ledger");
    int format = s == HEADER2 ? 1 : s == HEADERN ? 2 : 0;
    require(format, "unrecognized TSV header");
    out.data(MAGIC, 8); out.byte(format); out.var(choices); out.var(s.size()); out.data(s.data(), s.size());
    int current_group = -1, current_deleted = -1; U64 rows = 0, groups = 0, runs = 0, count = 0;
    Event last;
    while (in.line(s)) {
        std::array<std::string_view, 8> f;
        require(split(std::string_view(s.data(), s.size() - 1), f) == (format == 1 ? 8 : 7), "incorrect TSV field count");
        int group = integer(f[0]), deleted = integer(f[1]);
        require(group >= 0 && deleted >= 0, "negative group or deleted state");
        if (group != current_group) {
            if (count) { write_run(out, last, count); ++runs; count = 0; }
            int degree = format == 1 ? 2 : 1;
            if (format == 2) for (char c : f[2]) degree += c == ',';
            require(degree <= MAXDEGREE, "degree exceeds codec bound");
            out.byte(0); out.var(group); out.var(deleted); out.var(degree);
            current_group = group; current_deleted = deleted; ++groups;
        }
        require(deleted == current_deleted, "deleted state changes within group");
        int offset = format == 1 ? 4 : 3;
        Event e;
        e.outcome = f[offset] == "branch" ? 0 : f[offset] == "prune" ? 1 : f[offset] == "survivor" ? 2 : -1;
        require(e.outcome >= 0, "unknown outcome");
        e.value = integer(f[offset + 1]); e.reason = integer(f[offset + 2]);
        require(e.reason >= 0, "negative reason");
        if (count && !(e == last)) { write_run(out, last, count); ++runs; count = 0; }
        last = e; ++count; ++rows;
    }
    if (count) { write_run(out, last, count); ++runs; }
    Digest digest = in.sha.finish();
    out.byte(2); out.var(in.bytes); out.var(rows); out.var(groups); out.data(digest.data(), digest.size()); out.close();
    std::cout << "{\"format\":\"proveit-dfs-ledger-v1\",\"choices\":" << choices
              << ",\"raw_bytes\":" << in.bytes << ",\"event_rows\":" << rows
              << ",\"group_count\":" << groups << ",\"event_runs\":" << runs
              << ",\"raw_sha256\":\"" << hex(digest) << "\"}\n";
}

struct Sink {
    FILE *file = nullptr;
    std::string buffer;
    Sha256 sha;
    U64 bytes = 0;
    explicit Sink(const char *name) {
        if (name) { file = std::fopen(name, "wb"); require(file, "cannot open unpacked output"); }
        buffer.reserve(BUFSIZE + 1024);
    }
    ~Sink() { if (file) std::fclose(file); }
    void flush() {
        if (buffer.empty()) return;
        sha.update(buffer.data(), buffer.size()); bytes += buffer.size();
        if (file) require(std::fwrite(buffer.data(), 1, buffer.size(), file) == buffer.size(), "unpacked output write failed");
        buffer.clear();
    }
    void literal(std::string_view s) { buffer.append(s.data(), s.size()); }
    void character(char c) { buffer += c; }
    void number(int n) { char b[32]; auto r = std::to_chars(b, b + sizeof(b), n); buffer.append(b, r.ptr); }
    void big(Big n) { char b[48]; char *p = b + sizeof(b); do { *--p = char('0' + n % 10); n /= 10; } while (n); buffer.append(p, b + sizeof(b)); }
    void endrow() { buffer += '\n'; if (buffer.size() >= BUFSIZE) flush(); }
    Digest finish() { flush(); if (file) require(std::fflush(file) == 0, "output flush failed"); return sha.finish(); }
};
using Assignment = std::array<int, MAXDEGREE>;
struct Group {
    int id, deleted, degree;
    U64 rows = 0, branches = 0, prunes = 0, survivors = 0, pending = 0;
};
void unpack(const char *packed, const char *raw) {
    GzReader in(packed); Sink out(raw); char magic[8]; in.data(magic, 8);
    require(std::memcmp(magic, MAGIC, 8) == 0, "unknown packed ledger magic");
    int format = in.byte(); require(format == 1 || format == 2, "unknown packed ledger format");
    int choices = in.integer(); require(choices >= 2 && choices <= 100000, "invalid choice count");
    U64 length = in.var(); require(length <= 65536, "header too long");
    std::string header(length, '\0'); in.data(header.data(), header.size());
    require(header == (format == 1 ? HEADER2 : HEADERN), "invalid stored header"); out.literal(header);
    std::vector<Assignment> stack;
    std::vector<Group> groups;
    std::array<Big, MAXDEGREE + 1> powers; powers[0] = 1;
    int degree = 0; U64 rows = 0, runs = 0;
    for (;;) {
        int tag = in.byte();
        if (tag == 0) {
            require(stack.empty(), "new group before previous DFS completed");
            Group group; group.id = in.integer(); group.deleted = in.integer(); group.degree = in.integer();
            require(groups.empty() || group.id == groups.back().id + 1, "nonconsecutive groups");
            require(group.degree >= 1 && group.degree <= MAXDEGREE && (format != 1 || group.degree == 2), "invalid group degree");
            groups.push_back(group); degree = group.degree;
            for (int k = 1; k <= degree; ++k) {
                require(powers[k-1] <= (~Big(0)) / choices, "assignment weight overflows 128 bits");
                powers[k] = powers[k-1] * choices;
            }
            Assignment a; a.fill(-1); stack.push_back(a);
        } else if (tag == 1) {
            require(!groups.empty(), "events before first group");
            U64 count = in.var(); require(count > 0, "empty event run"); ++runs;
            Event e; e.outcome = in.byte(); e.value = in.signedvar(); e.reason = in.integer();
            require(e.outcome <= 2, "unknown event code");
            Group &g = groups.back();
            while (count--) {
                require(!stack.empty(), "event after DFS completed");
                Assignment a = stack.back(); stack.pop_back();
                int unknown = 0; for (int k = 0; k < degree; ++k) unknown += a[k] < 0;
                out.number(g.id); out.character('\t'); out.number(g.deleted); out.character('\t');
                for (int k = 0; k < degree; ++k) { if (k) out.character(format == 1 ? '\t' : ','); out.number(a[k]); }
                out.character('\t');
                if (e.outcome == 0) {
                    require(e.value >= 0 && e.value < degree && a[e.value] == -1 && e.reason == 0, "invalid branch event");
                    out.literal("branch\t"); out.number(e.value); out.literal("\t0\t0"); ++g.branches;
                    for (int k = choices - 1; k >= 0; --k) { a[e.value] = k; stack.push_back(a); }
                } else if (e.outcome == 1) {
                    require(e.value >= 0, "invalid prune case");
                    out.literal("prune\t"); out.number(e.value); out.character('\t'); out.number(e.reason); out.character('\t'); out.big(powers[unknown]); ++g.prunes;
                } else {
                    require(e.value == -1 && e.reason == 0, "invalid survivor event");
                    out.literal("survivor\t-1\t0\t1"); ++g.survivors;
                }
                out.endrow(); ++rows; ++g.rows;
            }
        } else if (tag == 2) {
            U64 expected_bytes = in.var(), expected_rows = in.var(), expected_groups = in.var();
            Digest expected_digest; in.data(expected_digest.data(), expected_digest.size());
            require(in.optionalbyte() == -1, "trailing data after ledger footer");
            Digest digest = out.finish();
            require(out.bytes == expected_bytes, "reconstructed byte count mismatch");
            require(rows == expected_rows && groups.size() == expected_groups, "reconstructed event/group count mismatch");
            require(digest == expected_digest, "reconstructed SHA256 mismatch");
            if (!groups.empty()) groups.back().pending = stack.size();
            std::cout << "{\"verified\":true,\"raw_bytes\":" << out.bytes << ",\"event_rows\":" << rows
                      << ",\"event_runs\":" << runs << ",\"raw_sha256\":\"" << hex(digest) << "\",\"groups\":[";
            for (size_t k = 0; k < groups.size(); ++k) {
                const auto &g = groups[k]; if (k) std::cout << ',';
                std::cout << "{\"group\":" << g.id << ",\"deleted\":" << g.deleted << ",\"degree\":" << g.degree
                          << ",\"events\":" << g.rows << ",\"branches\":" << g.branches << ",\"prunes\":" << g.prunes
                          << ",\"survivors\":" << g.survivors << ",\"pending_nodes\":" << g.pending
                          << ",\"complete\":" << (g.pending ? "false" : "true") << '}';
            }
            std::cout << "]}\n"; return;
        } else fail("unknown record tag");
    }
}

int main(int argc, char **argv) {
    try {
        if (argc == 5 && std::string(argv[1]) == "pack") pack(argv[2], argv[3], integer(argv[4]));
        else if (argc == 3 && std::string(argv[1]) == "verify") unpack(argv[2], nullptr);
        else if (argc == 4 && std::string(argv[1]) == "unpack") unpack(argv[2], argv[3]);
        else fail("usage: helper pack RAW PACKED CHOICES | verify PACKED | unpack PACKED RAW");
        return 0;
    } catch (const std::exception &e) { std::cerr << "ledger_codec: " << e.what() << '\n'; return 1; }
}
