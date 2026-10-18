// Condensed detachment saturation from L = CCCpqrCCrpCsp (fast version of cdsearch.py).
// Formulas in Polish notation strings: 'C' = implication, variables 'a'+k (canonical order).
// Output: for each target found, the proof DAG as lines "id major minor formula" (id 0 = axiom).
// Usage: cdfast maxsize maxgiven target1 target2 ...
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <algorithm>
using namespace std;

struct Node { int op; int a, b; };  // op 0 = var (a = id), op 1 = imp
// tree as vector of nodes, root last
typedef vector<Node> Tree;

static int parseRec(const string& s, size_t& pos, Tree& t, map<char,int>& nm) {
    char c = s[pos++];
    if (c == 'C') { int x = parseRec(s, pos, t, nm); int y = parseRec(s, pos, t, nm); t.push_back({1, x, y}); return (int)t.size() - 1; }
    if (!nm.count(c)) { int k = (int)nm.size(); nm[c] = k; }
    t.push_back({0, nm[c], 0}); return (int)t.size() - 1;
}
static Tree parse(const string& s) { Tree t; size_t p = 0; map<char,int> nm; parseRec(s, p, t, nm); return t; }

// formula as string canonical: variables renamed by first occurrence
static void toStr(const Tree& t, int n, string& out, unordered_map<int,int>& ren) {
    if (t[n].op == 1) { out.push_back('C'); toStr(t, t[n].a, out, ren); toStr(t, t[n].b, out, ren); }
    else { auto it = ren.find(t[n].a); int k; if (it == ren.end()) { k = (int)ren.size(); ren[t[n].a] = k; } else k = it->second;
           if (k < 26) out.push_back('a' + k); else { out.push_back('#'); out.push_back('a' + k / 26); out.push_back('a' + k % 26); } }
}
static string canon(const Tree& t, int root) { string s; unordered_map<int,int> r; toStr(t, root, s, r); return s; }

// unification over a combined term store with substitution on variable ids
struct U {
    vector<Node> st; unordered_map<int,int> sub;  // var id -> node index
    int add(const Tree& t, int n, int off) {
        if (t[n].op == 0) { st.push_back({0, t[n].a + off, 0}); return (int)st.size() - 1; }
        int x = add(t, t[n].a, off), y = add(t, t[n].b, off); st.push_back({1, x, y}); return (int)st.size() - 1;
    }
    int walk(int n) { while (st[n].op == 0) { auto it = sub.find(st[n].a); if (it == sub.end()) break; n = it->second; } return n; }
    bool occurs(int v, int n) { n = walk(n); if (st[n].op == 0) return st[n].a == v; return occurs(v, st[n].a) || occurs(v, st[n].b); }
    bool unify(int x, int y) {
        x = walk(x); y = walk(y);
        if (x == y) return true;
        if (st[x].op == 0 && st[y].op == 0 && st[x].a == st[y].a) return true;
        if (st[x].op == 0) { if (occurs(st[x].a, y)) return false; sub[st[x].a] = y; return true; }
        if (st[y].op == 0) return unify(y, x);
        return unify(st[x].a, st[y].a) && unify(st[x].b, st[y].b);
    }
    void out(int n, string& s, unordered_map<int,int>& ren) {
        n = walk(n);
        if (st[n].op == 1) { s.push_back('C'); out(st[n].a, s, ren); out(st[n].b, s, ren); }
        else { auto it = ren.find(st[n].a); int k; if (it == ren.end()) { k = (int)ren.size(); ren[st[n].a] = k; } else k = it->second;
               if (k < 26) s.push_back('a' + k); else { s.push_back('#'); s.push_back('a' + k / 26); s.push_back('a' + k % 26); } }
    }
};

static int fsize(const string& s) { int n = 0; for (char c : s) if (c != '#') n++; return n; }

// one-way matching: is spec an instance of gen ?
static bool matchRec(const Tree& g, int gn, const Tree& sp, int sn, unordered_map<int,int>& m, const string& sps) {
    if (g[gn].op == 0) {
        // compare subtree structurally via canonical-free id: store first binding node, compare trees
        auto it = m.find(g[gn].a);
        if (it == m.end()) { m[g[gn].a] = sn; return true; }
        // structural equality of sp subtrees it->second and sn
        vector<pair<int,int>> stk{{it->second, sn}};
        while (!stk.empty()) { auto [x, y] = stk.back(); stk.pop_back();
            if (sp[x].op != sp[y].op) return false;
            if (sp[x].op == 0) { if (sp[x].a != sp[y].a) return false; }
            else { stk.push_back({sp[x].a, sp[y].a}); stk.push_back({sp[x].b, sp[y].b}); } }
        return true;
    }
    if (sp[sn].op != 1) return false;
    return matchRec(g, g[gn].a, sp, sp[sn].a, m, sps) && matchRec(g, g[gn].b, sp, sp[sn].b, m, sps);
}
static bool instanceOf(const string& spec, const string& gen) {
    Tree s = parse(spec), g = parse(gen); unordered_map<int,int> m;
    return matchRec(g, (int)g.size() - 1, s, (int)s.size() - 1, m, spec);
}

struct Item { string f; int major, minor; };

int main(int argc, char** argv) {
    int maxsize = atoi(argv[1]); int maxgiven = atoi(argv[2]);
    vector<string> targets; for (int i = 3; i < argc; i++) targets.push_back(argv[i]);
    vector<Item> items; unordered_map<string,int> seen;
    auto pushItem = [&](const string& f, int a, int b) { items.push_back({f, a, b}); seen[f] = (int)items.size() - 1; return (int)items.size() - 1; };
    string L = canon(parse("CCCpqrCCrpCsp"), (int)parse("CCCpqrCCrpCsp").size() - 1);
    pushItem(L, -1, -1);
    typedef pair<int,int> PI; priority_queue<PI, vector<PI>, greater<PI>> pq; pq.push({fsize(L), 0});
    vector<int> processed; vector<Tree> ptrees;
    vector<int> found(targets.size(), -1); int nfound = 0; int given = 0;
    while (!pq.empty() && given < maxgiven && nfound < (int)targets.size()) {
        int id = pq.top().second; pq.pop();
        const string f = items[id].f;
        bool sub = false;
        for (int p : processed) if (instanceOf(f, items[p].f)) { sub = true; break; }
        if (sub) continue;
        processed.push_back(id); ptrees.push_back(parse(f)); given++;
        for (size_t t = 0; t < targets.size(); t++) if (found[t] < 0 && instanceOf(targets[t], f)) {
            found[t] = id; nfound++; fprintf(stderr, "FOUND %s as %s (given %d)\n", targets[t].c_str(), f.c_str(), given); }
        if (given % 500 == 0) fprintf(stderr, "given %d size %d queue %zu items %zu\n", given, fsize(f), pq.size(), items.size());
        Tree ft = ptrees.back();
        for (size_t j = 0; j < processed.size(); j++) {
            for (int dir = 0; dir < 2; dir++) {
                int majId = dir ? processed[j] : id, minId = dir ? id : processed[j];
                const Tree& mj = dir ? ptrees[j] : ft; const Tree& mn = dir ? ft : ptrees[j];
                int mr = (int)mj.size() - 1; if (mj[mr].op != 1) continue;
                U u; int r1 = u.add(mj, mr, 0); int r2 = u.add(mn, (int)mn.size() - 1, 1000);
                if (!u.unify(u.st[r1].a, r2)) continue;
                string s; unordered_map<int,int> ren; u.out(u.st[r1].b, s, ren);
                if (fsize(s) > maxsize) continue;
                if (seen.count(s)) continue;
                int nid = pushItem(s, majId, minId); pq.push({fsize(s), nid});
            }
        }
    }
    // print proofs
    unordered_set<int> need; vector<int> stk;
    for (int t : found) if (t >= 0) stk.push_back(t);
    while (!stk.empty()) { int x = stk.back(); stk.pop_back(); if (need.count(x)) continue; need.insert(x);
        if (items[x].major >= 0) { stk.push_back(items[x].major); stk.push_back(items[x].minor); } }
    vector<int> ids(need.begin(), need.end()); sort(ids.begin(), ids.end());
    for (int x : ids) printf("N %d %d %d %s\n", x, items[x].major, items[x].minor, items[x].f.c_str());
    for (size_t t = 0; t < targets.size(); t++) printf("T %s %d\n", targets[t].c_str(), found[t]);
    return 0;
}
