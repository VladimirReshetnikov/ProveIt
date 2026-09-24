// Exact C++17 port of the recurrence proved in the accompanying article.
// Precondition: inputs are tuples of strings over {a,b,c}, with int-sized length.
// No search budget, timeout, or approximation is used. Cache policy affects speed
// only. The Python implementation provides the documented general-purpose API.
#pragma once
#include <algorithm>
#include <array>
#include <chrono>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using Tup = vector<string>;

static string keynorm(const Tup &parts) {
    string forward;
    for (const auto &part : parts) if (!part.empty()) {
        if (!forward.empty()) forward += '|';
        forward += part;
    }
    auto relabel = [](string key) {
        array<char, 256> mapping{};
        char next = 'a';
        for (char &c : key) if (c != '|') {
            auto i = static_cast<unsigned char>(c);
            if (!mapping[i]) mapping[i] = next++;
            c = mapping[i];
        }
        return key;
    };
    string backward = forward;
    reverse(backward.begin(), backward.end());
    return min(relabel(forward), relabel(backward));
}

static Tup unpack(const string &key) {
    Tup parts;
    string part;
    for (char c : key) {
        if (c == '|') {
            parts.push_back(part);
            part.clear();
        } else {
            part += c;
        }
    }
    if (!part.empty()) parts.push_back(part);
    return parts;
}

struct Parser {
    int r;
    long long misses = 0, hits = 0;
    unordered_map<string, bool> cache;

    explicit Parser(int arity) : r(arity) { cache.reserve(1000000); }

    bool accepts(const Tup &parts) { return get(keynorm(parts)); }

    bool get(const string &key) {
        auto found = cache.find(key);
        if (found != cache.end()) {
            ++hits;
            return found->second;
        }
        ++misses;
        bool answer = calculate(unpack(key));
        auto letters = key.size() - count(key.begin(), key.end(), '|');
        if (letters <= 18) cache.emplace(key, answer);
        return answer;
    }

    bool calculate(const Tup &parts) {
        int k = static_cast<int>(parts.size());
        if (!k) return true;
        if (k > r) return false;
        string word;
        for (const auto &s : parts) word += s;
        int n = static_cast<int>(word.size());
        array<int, 3> counts{};
        for (char c : word) ++counts[c-'a'];
        if (counts[0] != counts[1] || counts[0] != counts[2]) return false;

        // One physical endpoint of each of the three letters.
        array<vector<pair<int, int>>, 3> endpoints;
        for (int i=0; i<k; ++i) {
            endpoints[parts[i][0]-'a'].push_back({i, 0});
            if (parts[i].size() > 1)
                endpoints[parts[i].back()-'a'].push_back(
                    {i, static_cast<int>(parts[i].size())-1});
        }
        for (auto a : endpoints[0])
            for (auto b : endpoints[1])
                for (auto c : endpoints[2]) {
                    Tup child = parts;
                    array<pair<int, int>, 3> removed = {a, b, c};
                    // Erasing from larger indices first prevents shifts.
                    sort(removed.rbegin(), removed.rend());
                    for (auto [i, j] : removed) child[i].erase(j, 1);
                    if (accepts(child)) return true;
                }

        vector<int> starts;
        int offset = 0;
        for (const auto &s : parts) {
            starts.push_back(offset);
            offset += static_cast<int>(s.size());
        }
        vector<pair<int, int>> prefix(n+1);
        for (int i=0; i<n; ++i) {
            auto [a, b] = prefix[i];
            a += (word[i]=='a') - (word[i]=='c');
            b += (word[i]=='b') - (word[i]=='c');
            prefix[i+1] = {a, b};
        }
        for (int p=0; p<n; ++p) for (int q=p+3; q<=n; q+=3) {
            if (q-p == n || prefix[p] != prefix[q]) continue;
            Tup outside, inside;
            for (int i=0; i<k; ++i) {
                const string &s = parts[i];
                int size = static_cast<int>(s.size());
                int lo = clamp(p-starts[i], 0, size);
                int hi = clamp(q-starts[i], 0, size);
                if (lo) outside.push_back(s.substr(0, lo));
                if (hi > lo) inside.push_back(s.substr(lo, hi-lo));
                // Do NOT merge this suffix with the exposed prefix.
                if (hi < size) outside.push_back(s.substr(hi));
            }
            if (outside.size() <= static_cast<size_t>(r)
                    && inside.size() <= static_cast<size_t>(r)
                    && accepts(inside) && accepts(outside)) return true;
        }

        // An inverse regrouping step: one new genuine component boundary.
        if (k < r) for (int i=0; i<k; ++i)
            for (int cut=1; cut<static_cast<int>(parts[i].size()); ++cut) {
                Tup finer;
                for (int j=0; j<k; ++j) {
                    if (j == i) {
                        finer.push_back(parts[i].substr(0, cut));
                        finer.push_back(parts[i].substr(cut));
                    } else {
                        finer.push_back(parts[j]);
                    }
                }
                if (accepts(finer)) return true;
            }
        return false;
    }
};
