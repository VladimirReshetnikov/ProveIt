// Fast condensed-detachment given-clause prover (untrusted search helper).
// Axiom: Lukasiewicz's CCCpqrCCrpCsp (the machines' rho8).  Formulas are in
// Polish notation: 'C' = implication, variables are small ints.
//
//   lukasiewicz_search MAXSIZE RATIO MAXGIVEN NAME=TARGET ...
//
// Given clauses are picked lightest-first, except every RATIO-th pick, which
// takes the oldest unprocessed clause.  New clauses are kept unless an exact
// duplicate or subsumed by an already processed clause.  Output: proof lines
// "id major minor formula" for the derivation of each target, then
// "TARGET name id".  lukasiewicz_cd.py --from-proof replays and checks them.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
using namespace std;

typedef vector<int> F; // prefix: -1 = C, >=0 variable

static int fsize(const F& f) { return (int)f.size(); }

// parse "CCCpqrCCrpCsp" style
F parseF(const char* s) {
    F f; unordered_map<char,int> m;
    for (; *s; ++s) {
        if (*s == 'C') f.push_back(-1);
        else { auto it = m.find(*s); int v; if (it == m.end()) { v = (int)m.size(); m[*s] = v; } else v = it->second; f.push_back(v); }
    }
    return f;
}

string show(const F& f) {
    string s; for (int x : f) { if (x < 0) s += 'C'; else s += (char)('a' + (x % 26)), s += (x >= 26 ? "'" : ""); } return s;
}

// subterm end index
int skip(const F& f, int i) { int need = 1; while (need) { if (f[i] < 0) need += 1; else need -= 1; ++i; } return i; }

struct Subst { vector<int> bindF; vector<int> bindPos; }; // var -> (formula id 0/1, start pos), -1 unbound

// Unify subterm a (in A at pos ia) with subterm b (in B at ib); variables of A are 0..na-1, of B offset by na.
struct Unifier {
    const F* T[2];
    int off; // variables of T[1] are shifted by off
    vector<int> bf, bp; // binding: which formula, position
    bool init(const F* a, const F* b, int na, int nb) {
        T[0] = a; T[1] = b; off = na; bf.assign(na + nb, -1); bp.assign(na + nb, -1); return true;
    }
    int varAt(int w, int p) { int v = (*T[w])[p]; return w == 0 ? v : v + off; }
    // deref: (w,p) is a position; if variable bound, follow
    void deref(int& w, int& p) {
        while ((*T[w])[p] >= 0) { int v = varAt(w, p); if (bf[v] < 0) return; int nw = bf[v], np = bp[v]; w = nw; p = np; }
    }
    bool occurs(int v, int w, int p) {
        deref(w, p);
        if ((*T[w])[p] >= 0) return varAt(w, p) == v;
        int q = p + 1; if (occurs(v, w, q)) return true; q = skip(*T[w], q); return occurs(v, w, q);
    }
    bool unify(int w1, int p1, int w2, int p2) {
        deref(w1, p1); deref(w2, p2);
        bool v1 = (*T[w1])[p1] >= 0, v2 = (*T[w2])[p2] >= 0;
        if (v1 && v2 && varAt(w1, p1) == varAt(w2, p2)) return true;
        if (v1) { int v = varAt(w1, p1); if (occurs(v, w2, p2)) return false; bf[v] = w2; bp[v] = p2; return true; }
        if (v2) { int v = varAt(w2, p2); if (occurs(v, w1, p1)) return false; bf[v] = w1; bp[v] = p1; return true; }
        int a = p1 + 1, b = p2 + 1;
        if (!unify(w1, a, w2, b)) return false;
        return unify(w1, skip(*T[w1], a), w2, skip(*T[w2], b));
    }
    void build(int w, int p, F& out, int limit) {
        if ((int)out.size() > limit) return;
        deref(w, p);
        int x = (*T[w])[p];
        if (x >= 0) { out.push_back(varAt(w, p)); return; }
        out.push_back(-1); int q = p + 1; build(w, q, out, limit); build(w, skip(*T[w], q), out, limit);
    }
};

F canon(const F& f, int& nv) {
    unordered_map<int,int> m; F g; g.reserve(f.size());
    for (int x : f) { if (x < 0) g.push_back(-1); else { auto it = m.find(x); if (it == m.end()) { int v = (int)m.size(); m[x] = v; g.push_back(v); } else g.push_back(it->second); } }
    nv = (int)m.size(); return g;
}

int nvars(const F& f) { int n = 0; for (int x : f) if (x + 1 > n) n = x + 1; return n; }

// one-way matching: does general g subsume specific s?
bool matchAt(const F& g, int& i, const F& s, int& j, vector<int>& bindStart, vector<int>& bindEnd) {
    int x = g[i];
    if (x >= 0) {
        int e = skip(s, j);
        if (bindStart[x] < 0) { bindStart[x] = j; bindEnd[x] = e; }
        else { int l1 = bindEnd[x] - bindStart[x]; if (l1 != e - j) return false; if (memcmp(&s[bindStart[x]], &s[j], l1 * sizeof(int))) return false; }
        i++; j = e; return true;
    }
    if (s[j] >= 0) return false;
    i++; j++;
    if (!matchAt(g, i, s, j, bindStart, bindEnd)) return false;
    return matchAt(g, i, s, j, bindStart, bindEnd);
}
bool subsumes(const F& g, const F& s) {
    if (g.size() > s.size()) return false;
    vector<int> bs(nvars(g), -1), be(nvars(g), -1);
    int i = 0, j = 0; return matchAt(g, i, s, j, bs, be);
}

struct Clause { F f; int major, minor; int nv; };
vector<Clause> cls;

struct Hash { size_t operator()(const F& f) const { size_t h = 1469598103934665603ULL; for (int x : f) { h ^= (size_t)(x + 7); h *= 1099511628211ULL; } return h; } };

int main(int argc, char** argv) {
    int maxSize = argc > 1 ? atoi(argv[1]) : 31;   // in Polish symbols
    int ratio = argc > 2 ? atoi(argv[2]) : 5;
    long maxGiven = argc > 3 ? atol(argv[3]) : 200000;
    vector<string> tnames; vector<F> targets;
    for (int k = 4; k < argc; ++k) { string a = argv[k]; auto c = a.find('='); tnames.push_back(a.substr(0, c)); targets.push_back(parseF(a.substr(c + 1).c_str())); }
    F L = parseF("CCCpqrCCrpCsp");
    cls.push_back({L, -1, -1, nvars(L)});
    unordered_set<F, Hash> seen; seen.insert(L);
    // weight queue (size, id), age queue
    priority_queue<pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>>> wq; wq.push({fsize(L), 0});
    int ageNext = 0;
    vector<int> usable; vector<char> done(1, 0);
    vector<int> found(targets.size(), -1); int nfound = 0;
    // retained index by size for forward subsumption
    vector<vector<int>> bySize(maxSize + 2);
    bySize[fsize(L)].push_back(0);
    long given = 0;
    while (nfound < (int)targets.size() && given < maxGiven) {
        int id = -1;
        if (ratio > 0 && given % ratio == ratio - 1) {
            while (ageNext < (int)cls.size() && done[ageNext]) ageNext++;
            if (ageNext < (int)cls.size()) id = ageNext;
        }
        if (id < 0) {
            while (!wq.empty() && done[wq.top().second]) wq.pop();
            if (wq.empty()) break;
            id = wq.top().second; wq.pop();
        }
        done[id] = 1;
        usable.push_back(id); given++;
        if (given % 200 == 0) { fprintf(stderr, "given %ld kept %zu found %d\n", given, cls.size(), nfound); }
        for (size_t ui = 0; ui < usable.size(); ++ui) {
            int u = usable[ui];
            for (int dir = 0; dir < 2; ++dir) {
                int maj = dir ? u : id, mn = dir ? id : u;
                if (dir && u == id) continue;
                const F& M = cls[maj].f; if (M[0] >= 0) continue;
                const F& N = cls[mn].f;
                Unifier U; U.init(&M, &N, cls[maj].nv, cls[mn].nv);
                if (!U.unify(0, 1, 1, 0)) continue;
                F out; out.reserve(64);
                U.build(0, skip(M, 1), out, maxSize);
                if ((int)out.size() > maxSize) continue;
                int nv; F g = canon(out, nv);
                if (seen.count(g)) continue;
                // forward subsumption by retained clauses of size <= |g|
                bool sub = false;
                for (int s = 1; s <= (int)g.size() && !sub; ++s)
                    for (int c : bySize[s]) if (done[c] && subsumes(cls[c].f, g)) { sub = true; break; }
                if (sub) continue;
                seen.insert(g);
                int nid = (int)cls.size();
                cls.push_back({g, maj, mn, nv}); done.push_back(0);
                bySize[g.size()].push_back(nid);
                wq.push({(int)g.size(), nid});
                for (size_t t = 0; t < targets.size(); ++t)
                    if (found[t] < 0 && subsumes(g, targets[t])) { found[t] = nid; nfound++; fprintf(stderr, "found %s at %d: %s\n", tnames[t].c_str(), nid, show(g).c_str()); }
            }
        }
    }
    // print needed derivation
    vector<char> need(cls.size(), 0); vector<int> st;
    for (int t : found) if (t >= 0) st.push_back(t);
    while (!st.empty()) { int x = st.back(); st.pop_back(); if (need[x]) continue; need[x] = 1; if (cls[x].major >= 0) { st.push_back(cls[x].major); st.push_back(cls[x].minor); } }
    for (size_t i = 0; i < cls.size(); ++i) if (need[i]) printf("%zu %d %d %s\n", i, cls[i].major, cls[i].minor, show(cls[i].f).c_str());
    for (size_t t = 0; t < targets.size(); ++t) printf("TARGET %s %d\n", tnames[t].c_str(), found[t]);
    return nfound == (int)targets.size() ? 0 : 1;
}
