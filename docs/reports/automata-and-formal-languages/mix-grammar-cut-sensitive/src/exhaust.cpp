// Exhaustive enumeration modulo the six alphabet permutations and reversal.
// Build: c++ -O3 -std=c++17 src/exhaust.cpp -o build/mix_exhaust
// Run:   build/mix_exhaust 7 > data/cpp_through21.json
#include "mix_parser.hpp"
#include <cstdint>
#include <stdexcept>

static string renamed(string word) {
    array<char, 256> mapping{};
    char next = 'a';
    for (char &c : word) {
        auto i = static_cast<unsigned char>(c);
        if (!mapping[i]) mapping[i] = next++;
        c = mapping[i];
    }
    return word;
}

static uint64_t choose(int n, int k) {
    uint64_t answer = 1;
    for (int i = 1; i <= k; ++i) answer = answer * (n - k + i) / i;
    return answer;
}

struct Result {
    int length;
    uint64_t representatives = 0, words = 0, bad2 = 0, bad3 = 0;
    double seconds = 0;
};

static Result exhaust(int k, Parser &p2, Parser &p3) {
    Result result{3*k};
    if (k == 0) {
        result.representatives = result.words = 1;
        if (!p2.accepts({""}) || !p3.accepts({""}))
            throw runtime_error("empty-word regression");
        return result;
    }
    string word;
    array<int,3> counts{};
    auto started = chrono::steady_clock::now();
    auto visit = [&]() {
        string reversed = word;
        reverse(reversed.begin(), reversed.end());
        reversed = renamed(reversed);
        // 'word' is already canonical under alphabet permutations.
        if (word > reversed) return;
        uint64_t weight = (word == reversed) ? 6 : 12;
        result.words += weight;
        ++result.representatives;
        if (p2.cache.size() > 2000000) p2.cache.clear();
        if (!p2.accepts({word})) {
            result.bad2 += weight;
            // Monotonicity A_2 -> A_3 lets us omit known positive queries.
            if (!p3.accepts({word})) {
                result.bad3 += weight;
                cerr << "REJECTED_R3 " << word << '\n';
            }
        }
        if (result.representatives % 1000000 == 0)
            cerr << "PROGRESS length=" << 3*k
                 << " orbits=" << result.representatives
                 << " words=" << result.words << '\n';
    };
    // Restricted-growth words: a first occurs before b, and b before c.
    auto generate = [&](auto &&self, int seen) -> void {
        if (word.size() == static_cast<size_t>(3*k)) {
            visit();
            return;
        }
        for (int c = 0; c < 3; ++c) if (counts[c] < k && c <= seen) {
            ++counts[c];
            word.push_back(static_cast<char>('a' + c));
            self(self, max(seen, c + 1));
            word.pop_back();
            --counts[c];
        }
    };
    generate(generate, 0);
    uint64_t expected = choose(3*k, k) * choose(2*k, k);
    if (result.words != expected) throw runtime_error("orbit-weight count mismatch");
    result.seconds = chrono::duration<double>(chrono::steady_clock::now()-started).count();
    cerr << "COMPLETE length=" << 3*k << " words=" << result.words
         << " rejected_r2=" << result.bad2 << " rejected_r3=" << result.bad3
         << " seconds=" << result.seconds << '\n';
    return result;
}

int main(int argc, char **argv) {
    try {
        if (argc >= 3 && string(argv[1]) == "--check") {
            int r = stoi(argv[2]);
            if (r < 1) throw runtime_error("arity must be positive");
            Tup parts;
            for (int i=3; i<argc; ++i) {
                string s = argv[i];
                if (s.find_first_not_of("abc") != string::npos)
                    throw runtime_error("invalid alphabet");
                parts.push_back(s);
            }
            Parser parser(r);
            cout << (parser.accepts(parts) ? "true" : "false") << '\n';
            return 0;
        }
        int max_k = argc == 2 ? stoi(argv[1]) : 5;
        if (max_k < 0 || max_k > 10)
            throw runtime_error("max_k must be between 0 and 10; 7 means length 21");
        Parser p2(2), p3(3);
        cout << "{\n  \"complete\": true,\n  \"max_length\": " << 3*max_k
             << ",\n  \"results\": [\n";
        for (int k=0; k<=max_k; ++k) {
            auto t = exhaust(k, p2, p3);
            cout << "    {\"length\": " << t.length
                 << ", \"renaming_reversal_orbits\": " << t.representatives
                 << ", \"total_words\": " << t.words
                 << ", \"rejected_r2\": " << t.bad2
                 << ", \"rejected_r3\": " << t.bad3
                 << ", \"seconds\": " << t.seconds << "}"
                 << (k == max_k ? "\n" : ",\n") << flush;
        }
        cout << "  ]\n}\n";
        return 0;
    } catch (const exception &error) {
        cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
