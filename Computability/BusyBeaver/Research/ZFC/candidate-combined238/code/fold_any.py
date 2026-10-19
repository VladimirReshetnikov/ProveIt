"""Finite premises of the guarded 169 -> 80 fold, for ANY old table and its folded table.

Parameterized re-implementation of Source 101's verification/verify_guarded_fold239.py
(intake 172). Unchanged mathematics: the syntactic invariant (67/80/91/169 left bits)
closed under every old transition on all 9-cell windows; the four guarded blocks on all
admitted 5-cell windows with exact paths; one-step commutation of every other old row;
a checkpoint-by-checkpoint comparison of the whole old blank prefix with the clock
formula 4*V(80/0) + 2*V(169/0) + 4*V(169/1) + 8*V(91/1). The hash pins and the
480/478/476 and 409,691/409,835 constants are replaced by values computed from the tables.
Usage: fold_any.py OLD NEW OUT.json   (inherited labels; start 95, halt 254)
"""
import itertools, json, sys
from collections import Counter

def parse(p):
    T = {}
    for line in open(p, encoding="ascii"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        assert (int(q), int(b)) not in T
        T[int(q), int(b)] = (int(w), 1 if d == "R" else -1, int(z))
    S = {q for q, _ in T}
    assert set(T) == {(q, b) for q in S for b in (0, 1)} and {z for *_, z in T.values()} - S == {254}
    return T

def phi(q): return 80 if q == 169 else q

def inv(q, h, t):
    return ((q != 67 or t[h-1] == 0) and (q != 80 or (t[h-1] == 1 and t[h-2] == 0))
            and (q != 91 or (t[h-1] == 1 and t[h-2] == 1 and t[h-3] == 0))
            and (q != 169 or t[h-1] == 0))

def local(T, q, t, n):
    t = dict(t); h = 0; tr = []
    for _ in range(n):
        assert h in t and q != 254
        b = t[h]; w, d, z = T[q, b]; tr.append(q); t[h] = w; q = z; h += d
    return (q, h, t), tr

def step(T, q, h, ones):
    w, d, z = T[q, int(h in ones)]
    (ones.add if w else ones.discard)(h)
    return z, h + d

old, new = parse(sys.argv[1]), parse(sys.argv[2])
assert len(new) == len(old) - 2 and 169 in {q for q, _ in old} and 169 not in {q for q, _ in new}
expected = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in old.items() if q != 169}
expected[80, 0] = (0, -1, 106); expected[91, 1] = (1, -1, 167)
assert new == expected, "construction mismatch"
inc = {q: sorted([p, b, w, d] for (p, b), (w, d, z) in old.items() if z == q) for q in (67, 80, 91, 169)}
assert inc == {67: [[52, 0, 0, 1], [124, 0, 0, 1]], 80: [[67, 1, 1, 1]], 91: [[80, 1, 1, 1]],
               169: [[147, 0, 0, 1]]}, ("predecessor inventory changed", inc)
states = {q for q, _ in old}; invchecks = 0
for vals in itertools.product((0, 1), repeat=9):
    t = dict(zip(range(-4, 5), vals)); assert inv(95, 0, t)
    for q in states:
        if not inv(q, 0, t):
            continue
        w, d, z = old[q, t[0]]; u = dict(t); u[0] = w
        assert inv(z, d, u), ("invariant closure", q, vals); invchecks += 1
specs = [(80, 0, {-1: 1}, 5, [80, 106, 92, 107, 125, 25]),
         (169, 0, {-1: 0}, 3, [80, 106, 93, 57]),
         (169, 1, {-1: 0, 1: 1}, 5, [80, 91, 167, 151, 173, 56]),
         (91, 1, {-3: 0, -2: 1, -1: 1}, 9, [91, 167, 151, 24, 36, 54, 71, 82, 94, 50])]
blocks = []
for q, b, guard, n, path in specs:
    adm = 0
    for vals in itertools.product((0, 1), repeat=5):
        t = dict(zip(range(-3, 2), vals))
        if t[0] != b or any(t[x] != v for x, v in guard.items()):
            continue
        goal, _ = local(old, q, t, 1); act, tr = local(new, phi(q), t, n)
        assert act == (phi(goal[0]), goal[1], goal[2]), ("block mismatch", q, b, vals)
        assert tr + [act[0]] == path, ("path mismatch", q, b, tr)
        adm += 1
    assert adm > 0; blocks.append([q, b, n, adm])
exc = {(q, b) for q, b, *_ in specs}; ordinary = 0
for (q, b), (w, d, z) in old.items():
    if (q, b) in exc:
        continue
    assert new[phi(q), b] == (w, d, phi(z)), ("noncommuting row", q, b); ordinary += 1
assert ordinary == len(old) - 4
W = {-6, 176}; pos = 177
for v in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
    pos += 1; W.update(range(pos, pos + v + 1)); pos += v + 1
qo = qn = 95; ho = hn = 0; to, tn = set(), set(); cnt = Counter(); nsteps = 0; tick = 0
cost = {(q, b): n for q, b, _g, n, _p in specs}
while not ((qo, ho) == (96, -5) and to == W):
    assert qo != 254 and tick < 3_000_000
    assert (phi(qo), ho, to) == (qn, hn, tn), ("checkpoint", tick)
    key = (qo, int(ho in to)); n = cost.get(key, 1); cnt[key] += 1
    if key == (169, 1):
        assert ho + 1 in to, ("blank guard", tick)
    qo, ho = step(old, qo, ho, to)
    for _ in range(n):
        qn, hn = step(new, qn, hn, tn)
    nsteps += n; tick += 1
assert (phi(qo), ho, to) == (qn, hn, tn)
extra = 4 * cnt[80, 0] + 2 * cnt[169, 0] + 4 * cnt[169, 1] + 8 * cnt[91, 1]
assert nsteps == tick + extra
out = {"status": "PASS_EXACT_GUARDED_POSITIVE_BLOCK_CERTIFICATE", "old_rows": len(old),
       "new_rows": len(new), "invariant_window_checks": invchecks, "blocks": blocks,
       "ordinary_commuting_rows": ordinary, "old_boot_steps": tick, "new_boot_steps": nsteps,
       "exceptional_visits": {f"{q}/{b}": cnt[q, b] for q, b in sorted(exc)}}
json.dump(out, open(sys.argv[3], "w"), indent=2)
print(json.dumps(out, indent=2))
