"""Condensed-detachment search from Lukasiewicz's single axiom L = CCCpqrCCrpCsp (the AX row rho8),
emitting thm254 derivations (code level) of target implicational theorems.

Formulas: ('v', n) or ('i', A, B).  A proof is ('ax',) or ('D', major, minor) (condensed detachment:
major = A -> B, minor = C, unify A with C after renaming apart, conclude the most general B).

Usage: python cdsearch.py      prints proofs of K, S, Peirce, B (syllogism) as Coq terms.
"""
import itertools, sys

def V(n): return ('v', n)
def I(a, b): return ('i', a, b)

def parse(s):
    """Polish notation: C = implication, lowercase letters = variables."""
    pos = 0
    names = {}
    def go():
        nonlocal pos
        c = s[pos]; pos += 1
        if c == 'C':
            a = go(); b = go(); return I(a, b)
        if c not in names: names[c] = len(names)
        return V(names[c])
    f = go(); assert pos == len(s); return f

def show(f):
    if f[0] == 'v': return 'pqrstuvwxyzabcdefghijklmno'[f[1] % 26] + ('' if f[1] < 26 else str(f[1]))
    return 'C' + show(f[1]) + show(f[2])

def vars_of(f, acc=None):
    if acc is None: acc = set()
    if f[0] == 'v': acc.add(f[1])
    else: vars_of(f[1], acc); vars_of(f[2], acc)
    return acc

def subst(f, s):
    if f[0] == 'v':
        return subst(s[f[1]], s) if f[1] in s else f
    return I(subst(f[1], s), subst(f[2], s))

def walk(f, s):
    while f[0] == 'v' and f[1] in s: f = s[f[1]]
    return f

def occurs(v, f, s):
    f = walk(f, s)
    if f[0] == 'v': return f[1] == v
    return occurs(v, f[1], s) or occurs(v, f[2], s)

def unify(a, b, s):
    a = walk(a, s); b = walk(b, s)
    if a == b: return s
    if a[0] == 'v':
        if occurs(a[1], b, s): return None
        s = dict(s); s[a[1]] = b; return s
    if b[0] == 'v': return unify(b, a, s)
    s = unify(a[1], b[1], s)
    return None if s is None else unify(a[2], b[2], s)

def rename(f, off):
    if f[0] == 'v': return V(f[1] + off)
    return I(rename(f[1], off), rename(f[2], off))

def canon(f):
    m = {}
    def go(g):
        if g[0] == 'v':
            if g[1] not in m: m[g[1]] = len(m)
            return V(m[g[1]])
        return I(go(g[1]), go(g[2]))
    return go(f)

def size(f):
    return 1 if f[0] == 'v' else 1 + size(f[1]) + size(f[2])

def instance_of(spec, gen):
    """is spec an instance of gen?  (one-way matching)"""
    s = {}
    def m(g, t):
        if g[0] == 'v':
            if g[1] in s: return s[g[1]] == t
            s[g[1]] = t; return True
        return t[0] == 'i' and m(g[1], t[1]) and m(g[2], t[2])
    return m(gen, spec)

def detach(major, minor):
    if major[0] != 'i': return None
    minor = rename(minor, 1000)
    s = unify(major[1], minor, {})
    if s is None: return None
    return canon(subst_full(major[2], s))

def subst_full(f, s):
    f = walk(f, s)
    if f[0] == 'v': return f
    return I(subst_full(f[1], s), subst_full(f[2], s))

def search(targets, maxsize=24, maxkept=4000, maxgiven=20000):
    """given-clause loop: smallest unprocessed formula first; forward subsumption by instance."""
    import heapq
    L = canon(parse('CCCpqrCCrpCsp'))
    tgt = {k: parse(v) for k, v in targets.items()}
    found = {}
    heap = [(size(L), 0, L, ('ax',))]
    cnt = 1
    processed = []
    allf = [L]
    given = 0
    while heap and len(found) < len(tgt) and given < maxgiven:
        _, _, f, p = heapq.heappop(heap)
        if any(instance_of(f, h) for h, _ in processed):
            continue
        processed.append((f, p)); given += 1
        for k, t in tgt.items():
            if k not in found and instance_of(t, f):
                found[k] = (f, p)
                print('FOUND', k, show(f), 'given', given, flush=True)
                import pickle; pickle.dump(found, open('cd_found.pkl', 'wb'))
        if given % 200 == 0:
            print('given', given, 'size', size(f), 'heap', len(heap), flush=True)
        for g, q in processed:
            for (maj, pm), (mino, pn) in (((f, p), (g, q)), ((g, q), (f, p))):
                r = detach(maj, mino)
                if r is None or size(r) > maxsize: continue
                if any(instance_of(r, h) for h, _ in processed): continue
                heapq.heappush(heap, (size(r), cnt, r, ('D', pm, pn))); cnt += 1
    return found

def proof_size(p):
    return 1 if p[0] == 'ax' else 1 + proof_size(p[1]) + proof_size(p[2])

if __name__ == '__main__':
    targets = {'K': 'CpCqp', 'Peirce': 'CCCpqpp', 'B': 'CCpqCCqrCpr', 'S': 'CCpCqrCCpqCpr'}
    found = search(targets, maxsize=int(sys.argv[1]) if len(sys.argv) > 1 else 20)
    for k, (r, p) in found.items():
        print(k, show(r), 'proof steps', proof_size(p))
    import pickle
    pickle.dump(found, open('cd_found.pkl', 'wb'))
