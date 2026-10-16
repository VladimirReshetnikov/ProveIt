"""Register-machine simulation of the program DAG of source_local.py (Wade path semantics, as zf/tools/dag.py),
with optional acceleration of helper sub-DAGs by closed forms.

run(nodes, root, regs, accel)  executes the sub-DAG rooted at `root` from a fresh entry, with the
register dict `regs` (mutated), until it exits.  Exit = ('normal',) | ('break', k) | ('continue', k) |
('halt',), where break/continue k count the levels that escape `root` (path semantics: a leaf at
path Q+R (R inside root) that breaks j strips j zeros from Q+R; the zeros missing from R escape).

Acceleration: accel maps node name -> f(regs) -> exit; when the walk arrives FRESH at an accelerated
node (all bits below it zero), the closed form replaces the sub-DAG execution.  Every closed form is
checked against brute-force execution of its sub-DAG by validate_accel().
"""
import random
import bignum

def inc(P):
    """binary increment of the bit list P (MSB first); returns (P', overflow)."""
    P = list(P); i = len(P) - 1
    while i >= 0 and P[i] == 1:
        P[i] = 0; i -= 1
    if i < 0:
        return P, True
    P[i] = 1
    return P, False

def run(nodes, root, regs, accel=None, maxsteps=10**8, stats=None):
    P = []          # path bits relative to root; implicit trailing zeros
    steps = 0
    while True:
        steps += 1
        if steps > maxsteps:
            raise RuntimeError('step limit')
        # walk
        cur = ('node', root); d = 0
        while True:
            if cur[0] != 'node':
                break
            n = cur[1]
            if accel and n in accel and d > 0 and all(b == 0 for b in P[d:]):
                # fresh arrival at an accelerated node (not the root itself)
                if stats is not None:
                    stats[n] = stats.get(n, 0) + 1
                ex = accel[n](regs)
                Q = (P + [0] * d)[:d]
                res = _exit(Q, ex)
                if res[0] == 'esc':
                    return res[1]
                P = res[1]
                break
            b = P[d] if d < len(P) else 0
            cur = nodes[n][b]; d += 1
        else:
            pass
        if cur[0] == 'node':
            continue          # accelerated; P updated
        Q = (P + [0] * d)[:d]
        kind = cur[0]
        if kind == 'halt':
            return ('halt',)
        if kind == 'op':
            r = cur[1]
            if cur[2] == 'inc':
                regs[r] = bignum.add(regs[r], 1); ex = ('normal',)
            else:
                if regs[r] > 0:
                    regs[r] -= 1; ex = ('normal',)
                else:
                    ex = ('break', 1)
        elif kind == 'break':
            ex = ('break', cur[1])
        elif kind == 'continue':
            ex = ('continue', cur[1])
        else:
            raise ValueError(cur)
        res = _exit(Q, ex)
        if res[0] == 'esc':
            return res[1]
        P = res[1]

def _exit(Q, ex):
    """apply exit ex of the node at path Q; returns ('in', P') or ('esc', exit-of-root)."""
    kind = ex[0]
    if kind == 'halt':
        return ('esc', ('halt',))
    if kind == 'normal':
        P, ov = inc(Q)
        return ('esc', ('normal',)) if ov else ('in', P)
    k = ex[1]
    bit = 0 if kind == 'break' else 1
    P = list(Q)
    while k > 0 and P:
        if P.pop() == bit:
            k -= 1
    if k > 0:
        return ('esc', (kind, k))
    if kind == 'break':
        P, ov = inc(P)
        return ('esc', ('normal',)) if ov else ('in', P)
    return ('in', P)

# ---------------------------------------------------------------- closed forms

def tri(n):
    return n * (n + 1) // 2

def P2(a, b):
    """dual Cantor pairing of the source: P(a,b) = tri(a+b) + b."""
    return tri(a + b) + b

def isqrt(n):
    import math
    return math.isqrt(n)

def unP2(z):
    """inverse of P2."""
    s = (isqrt(8 * z + 1) - 1) // 2
    b = z - tri(s)
    return s - b, b

def inc_chain(nodes, e):
    """targets of a body that is a tree of inc ops (executed left to right), else None."""
    if e[0] == 'op' and e[2] == 'inc':
        return [e[1]]
    if e[0] == 'node':
        x, y = nodes[e[1]]
        a = inc_chain(nodes, x); b = inc_chain(nodes, y)
        if a is not None and b is not None:
            return a + b
    return None

def is_while(nodes, n):
    """match while_decnz(r, incs): (decnz r, continue 1) or (decnz r, (incs, continue 2)) with incs a
    tree of inc ops on registers other than r.  Returns (r, [targets with multiplicity]) or None."""
    car, cdr = nodes[n]
    if car[0] != 'op' or car[2] != 'decnz':
        return None
    r = car[1]
    if cdr == ('continue', 1):
        return r, []
    if cdr[0] != 'node':
        return None
    bc, bd = nodes[cdr[1]]
    if bd != ('continue', 2):
        return None
    ts = inc_chain(nodes, bc)
    if ts is None or r in ts:
        return None
    return r, ts

def mk_while(r, ts):
    def f(R):
        v = R[r]
        for t in ts:
            R[t] = bignum.add(R[t], v)
        R[r] = 0
        return ('normal',)
    return f

def is_unpair(nodes, n):
    """match the source's unpair(out1, out2, in1) loop:
    (decnz in1, ((inc out2, IFN), continue 2)),  IFN = ((decnz out1, break 1), while(out2 -> out1))."""
    car, cdr = nodes[n]
    if car[0] != 'op' or car[2] != 'decnz' or cdr[0] != 'node':
        return None
    in1 = car[1]
    b, c = nodes[cdr[1]]
    if c != ('continue', 2) or b[0] != 'node':
        return None
    x, ifn = nodes[b[1]]
    if not (x[0] == 'op' and x[2] == 'inc') or ifn[0] != 'node':
        return None
    out2 = x[1]
    t, w = nodes[ifn[1]]
    if t[0] != 'node' or w[0] != 'node':
        return None
    t1, t2 = nodes[t[1]]
    if not (t1[0] == 'op' and t1[2] == 'decnz' and t2 == ('break', 1)):
        return None
    out1 = t1[1]
    wm = is_while(nodes, w[1])
    if wm != (out2, [out1]):
        return None
    if len({in1, out1, out2}) != 3:
        return None
    return out1, out2, in1

def mk_unpair(out1, out2, in1):
    def f(R):
        z = bignum.add(bignum.P(R[out1], R[out2]), R[in1])
        R[out1], R[out2] = bignum.unP(z)
        R[in1] = 0
        return ('normal',)
    return f

def mk_pair(out, in1, in2):
    def f(R):
        R[out] = bignum.add(R[out], bignum.P(R[in1], R[in2]))
        R[in1] = 0; R[in2] = 0
        return ('normal',)
    return f

def mk_eqtest(a, b):
    """car of if_eq(a,b,body): zero both; normal exit (-> body) iff equal, else break 1."""
    def f(R):
        eq = R[a] == R[b]
        R[a] = 0; R[b] = 0
        return ('normal',) if eq else ('break', 1)
    return f

def build_accel(nodes):
    accel = {}; kinds = {}
    for n in nodes:
        w = is_while(nodes, n)
        if w:
            accel[n] = mk_while(*w); kinds[n] = ('while', w[0], tuple(w[1])); continue
        u = is_unpair(nodes, n)
        if u:
            accel[n] = mk_unpair(*u); kinds[n] = ('unpair',) + u; continue
        if n.startswith('pair(') and n.endswith(').0'):
            args = n[5:-3].split(',')
            accel[n] = mk_pair(*args); kinds[n] = ('pair',) + tuple(args); continue
        if n.startswith('if_eq(') and n.endswith(').0'):
            a, b = n[6:-3].split(',')[:2]
            car = nodes[n][0]
            assert car[0] == 'node'
            accel[car[1]] = mk_eqtest(a, b); kinds[car[1]] = ('eqtest', a, b)
    return accel, kinds

def validate_accel(nodes, regnames, accel, kinds, trials=300, vmax=12, seed=1):
    """compare every closed form with brute-force execution of its sub-DAG on random small registers."""
    rnd = random.Random(seed)
    bad = 0
    for n, f in accel.items():
        for t in range(trials):
            R = {r: rnd.randint(0, vmax) for r in regnames}
            if t < 20:   # also small corner values
                R = {r: rnd.randint(0, 2) for r in regnames}
            R1 = dict(R); R2 = dict(R)
            e1 = run(nodes, n, R1, accel=None)
            e2 = f(R2)
            if e1 != e2 or R1 != R2:
                bad += 1
                if bad < 10:
                    print('MISMATCH', n, kinds[n], R, e1, R1, e2, R2)
                break
    return bad
