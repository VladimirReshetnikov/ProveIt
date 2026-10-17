"""Completeness compiler (design + validation): code-level derivations of the machine calculus thm254
-> command lists -> program number, checked by running spec.enum_step from arbitrary retained states.

Commands:  MP(x) = (0, x)   DROP = (1, 0)   NIP = (2, 0)   AX(c; x, y, u) = (3 + c, x, y, u)
State at a boundary: (t, S, d, h) = (topwff, wffstack, param1, param2)  [pl, np handled by the runner].

Block contract  Build_X :  (T, S, 0, 0)  ->*  (X, S, 0, 0)   for all T, S   (or an earlier halt, which
can only happen at a NIP whose incoming cache is 1 = a derived theorem F).

Derivations (code level):  ('ax', 'bundle', a, b, c) | ('ax', 'rho<j>', a, b, c, u)  (j = 1..8; unused
parameters ignored) | ('gen', i, D) | ('mp', DA, DAB)   (DAB proves wim(A, B)).
"""
import random
import spec
from spec import P, unP, wim, wal

MP = lambda x: (0, x)
DROP = (1, 0)
NIP = (2, 0)
def AX(c, x, y, u): return (3 + c, x, y, u)

def conclusion(D):
    k = D[0]
    if k == 'ax':
        name = D[1]
        if name == 'bundle':
            a, b, c = D[2:5]
            return spec.bundle(a, b, c) if (c != a and c != b) else 0
        a, b, c, u = D[2:6]
        rows = spec.ax_rows(a, 0, b, c, u)        # [All(a,0), rho8, rho7, ..., rho1]
        j = int(name[3:])
        return rows[9 - j]
    if k == 'gen':
        return wal(D[1], conclusion(D[2]))
    if k == 'mp':
        A = conclusion(D[1]); I = conclusion(D[2])
        assert I == wim(A, conclusion_B(D)), 'mp: major premise is not A -> B'
        return conclusion_B(D)
    raise ValueError(D)

def conclusion_B(D):
    return D[3]

DISCARD = [MP(1), AX(1, 0, 0, 0)] + [NIP] * 10            # (T,S,0,0) -> (0,S,0,0)

def build(D):
    k = D[0]
    if k == 'ax':
        name = D[1]
        if name == 'bundle':
            a, b, c = D[2:5]
            return DISCARD + [AX(c, a, b, 0)] + [NIP] * 10
        a, b, c, u = D[2:6]
        j = int(name[3:])
        return DISCARD + [AX(c, a, b, u)] + [NIP] * j + [DROP] + [NIP] * (11 - j)
    if k == 'gen':
        i = D[1]
        return build(D[2]) + [DROP, NIP, AX(i, i, 0, 0)] + [NIP] * 9 + [DROP, NIP, NIP]
    if k == 'mp':
        B = D[3]
        return (build(D[1]) + [DROP] + build(D[2]) + [NIP, DROP, NIP, MP(B), AX(B, 0, 0, 0)]
                + [NIP] * 10 + [DROP, NIP, NIP])
    raise ValueError(D)

START = [AX(0, 1, 1, 0)]                                   # arbitrary (t,S,d,h) -> (R, S', 0, 0)
HALT_SUFFIX = [DROP, NIP, NIP]                             # (F,S,0,0) -> halt

def encode(cmds):
    """candidate number whose run executes cmds (first command read without the decrement)."""
    e = 0
    for c in reversed(cmds):
        v = e
        for f in reversed(c[1:]):
            v = P(f, v)
        e = spec.add(P(c[0], v), 1)
    return e - 1

def run_cmds(state, cmds, check_each=None):
    """run the command list inside one candidate starting from boundary state (t,S,d,h) by loading the
    encoded candidate as nextproof with prooflist = 0.  Returns final (t,S,d,h) or 'halt' with index."""
    t, S, d, h = state
    N = encode(cmds)
    s = (0, N, t, S, d, h)
    for i in range(len(cmds)):
        s2 = spec.enum_step(s)
        if s2 is None:
            return ('halt', i)
        s = s2
    assert s[0] == 0, 'candidate did not end where expected'
    return s[2:]

def rand_state(rnd):
    def code():
        k = rnd.random()
        if k < 0.3: return rnd.randint(0, 3)
        if k < 0.6: return rnd.randint(0, 10**6)
        return rnd.choice([spec.wim, spec.wel, spec.wal, spec.weq])(rnd.randint(0, 9), rnd.randint(0, 10**9))
    S = rnd.choice([0, P(code(), 0), P(code(), P(code(), rnd.randint(0, 99)))])
    return (code(), S, rnd.randint(0, 50), code())

def demo_derivations(rnd):
    a, b, c, u = (rnd.randint(0, 6) for _ in range(4))
    while c in (a, b):
        c += 1
    ds = [('ax', 'bundle', a, b, c)] + [('ax', f'rho{j}', a, b, c, u) for j in range(1, 9)]
    # gen of a leaf, and mp: GEN_x(rho5) then rho2 instance, MP -> A.x(c=a) -> A.x(...)
    r5 = ('ax', 'rho5', a, b, c, u)
    x = rnd.randint(0, 9)
    g = ('gen', x, r5)
    R5 = conclusion(r5)
    lhs, rhs = spec.weq(c, a), spec.wim(spec.wel(c, b), spec.wel(a, b))
    assert R5 == wim(lhs, rhs)
    qi = ('ax', 'rho2', x, lhs, rhs, 0)
    B = wim(wal(x, lhs), wal(x, rhs))
    assert conclusion(qi) == wim(conclusion(g), B)
    m = ('mp', g, qi, B)
    ds += [g, m, ('gen', rnd.randint(0, 3), m)]
    return ds

def main(n=300, seed=7):
    rnd = random.Random(seed)
    bad = 0; tested = 0
    for _ in range(n):
        for D in demo_derivations(rnd):
            X = conclusion(D)
            st = rand_state(rnd)
            st = (st[0], st[1], 0, 0)
            out = run_cmds(st, build(D))
            tested += 1
            if out[0] == 'halt':
                if st[0] != 1:
                    bad += 1; print('unexpected halt', D[:2], out)
                continue
            if not (out[0] == X and out[1] == st[1] and out[2] == 0 and out[3] == 0):
                bad += 1
                if bad < 5: print('CONTRACT FAIL', D[:2], st, out)
        # whole program from an arbitrary state: START + Build + DROP NIP NIP halts iff current = F
        st = rand_state(rnd)
        D = rnd.choice(demo_derivations(rnd))
        out = run_cmds(st, START + build(D))
        tested += 1
        if out[0] == 'halt':
            bad += 1; print('unexpected halt from arbitrary state', D[:2], out)
        elif not (out[0] == conclusion(D) and out[2] == 0 and out[3] == 0):
            bad += 1; print('START+Build fail', D[:2], st, out)
    # the halting suffix itself
    for _ in range(50):
        st = rand_state(rnd); S = st[1]
        out = run_cmds((1, S, 0, 0), HALT_SUFFIX)
        if out != ('halt', 2):
            bad += 1; print('suffix fail', out)
    print('block contracts tested', tested, 'failures', bad)
    print('example sizes: bundle leaf', len(build(('ax', 'bundle', 1, 2, 3))), 'commands; rho_j leaf',
          len(build(('ax', 'rho3', 1, 2, 3, 0))), '; GEN adds', len(build(('gen', 0, ('ax', 'bundle', 1, 2, 3)))) - 23,
          '; MP node adds', len(build(('mp', ('ax', 'bundle', 1, 2, 3), ('ax', 'bundle', 1, 2, 3), 0))) - 46)
    return bad

if __name__ == '__main__':
    import sys
    raise SystemExit(1 if main(int(sys.argv[1]) if len(sys.argv) > 1 else 100) else 0)
