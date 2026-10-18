"""Validate spec.enum_step against the register-machine semantics of the compiled program DAG.

1. every accelerated helper (while loops, unpair loops, pair, if_eq tests) = brute-force sub-DAG run
   on random small register files (arbitrary values, including nonzero outputs/scratch);
2. one run of main() from a boundary state (scratch1 = scratch2 = axiomcode = 0, other registers random)
   = enum_step, for random states; small states (MP/DROP/NIP and tiny AX-free cases) also fully
   unaccelerated;
3. the symbolic RPN extraction (extract_rpn.py) = spec's ax_rows/bundle on random parameters.

Usage: python validate.py [ntrials]
"""
import sys, random
from build_dag import load_dag
import rmsim, spec

REGS = ['nextproof', 'topwff', 'wffstack', 'axiomcode', 'param1', 'param2', 'scratch1', 'scratch2', 'prooflist']

def to_regs(s):
    pl, np, tw, ws, d, h = s
    return {'prooflist': pl, 'nextproof': np, 'topwff': tw, 'wffstack': ws, 'axiomcode': 0,
            'param1': d, 'param2': h, 'scratch1': 0, 'scratch2': 0}

def from_regs(R):
    return (R['prooflist'], R['nextproof'], R['topwff'], R['wffstack'], R['param1'], R['param2'])

def enc_cmds(cmds):
    """command list -> tail number e(cmds); a candidate number N with these commands is e(cmds) - 1
    (the first command is read without the decrement)."""
    e = 0
    for c in reversed(cmds):
        fields = list(c)
        v = e
        for f in reversed(fields[1:]):
            v = spec.P(f, v)
        e = 1 + spec.P(fields[0], v)
    return e

def rand_state(rnd, big):
    def small(m): return rnd.randint(0, m)
    def code():
        # a random formula-ish code, sometimes huge
        k = rnd.random()
        if k < 0.2: return small(3)
        if k < 0.5: return small(200)
        if not big: return small(2000)
        return rnd.choice([spec.wim, spec.wel, spec.wal, spec.weq])(small(50), small(10**6))
    cmd_kind = rnd.random()
    if cmd_kind < 0.2:
        ac = 0
    elif cmd_kind < 0.35:
        ac = 1
    elif cmd_kind < 0.55:
        ac = 2
    else:
        ac = 3 + small(6) if rnd.random() < 0.7 else 3 + small(40)
    x = small(5) if rnd.random() < 0.6 else small(60)
    tail = rnd.choice([0, 0, small(10), small(1000)])
    fields = [ac, x] + ([small(5), small(30)] if ac >= 3 else [])
    tw = code(); h = code(); d = small(6) if rnd.random() < 0.7 else small(50)
    if rnd.random() < 0.3:
        # make MP succeed
        ac = 0; fields = [0, x]; h = spec.wim(tw, d + x)
    if rnd.random() < 0.1 and ac >= 3:
        # force a gate collision
        fields[0] = 3 + (d + x if rnd.random() < 0.5 else h + fields[2])
    if rnd.random() < 0.05:
        h = 1
    v = tail
    for f in reversed(fields[1:]):
        v = spec.P(f, v)
    cell = spec.P(fields[0], v)
    ws = rnd.choice([0, small(50), spec.P(code(), spec.P(code(), small(100)))])
    if rnd.random() < 0.5:
        pl, np = cell + 1, small(100)          # within a candidate
    else:
        pl, np = 0, cell                        # candidate boundary: load nextproof
    return (pl, np, tw, ws, d, h)

def rand_small_state(rnd):
    """MP / DROP / NIP states small enough for unaccelerated unary simulation."""
    ac = rnd.choice([0, 0, 1, 2, 2])
    x = rnd.randint(0, 3)
    tw = rnd.randint(0, 6); d = rnd.randint(0, 3)
    h = rnd.choice([0, 1, 1, rnd.randint(0, 8), spec.wim(tw, d + x)])
    if spec.wim(tw, d + x) > 400:
        h = rnd.randint(0, 3)
    ws = rnd.choice([0, rnd.randint(0, 30), spec.P(rnd.randint(0, 5), rnd.randint(0, 5))])
    cell = spec.P(ac, spec.P(x, rnd.choice([0, 0, 1, 2])))
    if rnd.random() < 0.5:
        return (cell + 1, rnd.randint(0, 5), tw, ws, d, h)
    return (0, cell, tw, ws, d, h)

def check_rpn(rnd, n=200):
    import extract_rpn as E
    tw, ws, gates = E.axioms_symbolic(ninit=0)
    def ev(f, env):
        if isinstance(f, int): return f
        if isinstance(f, str): return env[f]
        h = f[0]; x = ev(f[1], env); y = ev(f[2], env)
        return {'Imp': spec.wim, 'Rel': spec.wel, 'All': spec.wal, 'Eq': spec.weq}[h](x, y)
    bad = 0
    for _ in range(n):
        a, b, B, c, q, T = (rnd.randint(0, 30) for _ in range(6))
        env = {'a': a, 'b': b, 'B': B, 'c': c, 'q': q, 'T': T}
        got = [ev(f, env) for f in ws] + [ev(tw, env)]
        want = [T] + spec.ax_rows(a, b, B, c, q) + [spec.bundle(a, B, c)]
        if got != want:
            bad += 1
    return bad

def main():
    ntr = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    rnd = random.Random(12345)
    nodes, regidx = load_dag()
    assert sorted(regidx) == sorted(REGS)
    accel, kinds = rmsim.build_accel(nodes)
    from collections import Counter
    print('accelerated nodes:', len(accel), Counter(k[0] for k in kinds.values()))
    bad = rmsim.validate_accel(nodes, REGS, accel, kinds)
    print('helper closed forms vs brute force: mismatches', bad)
    print('symbolic RPN vs spec rows: mismatches', check_rpn(rnd))
    # full unaccelerated runs on small states
    nbrute = 0; badb = 0
    for t in range(ntr // 4):
        s = rand_small_state(rnd)
        R = to_regs(s)
        try:
            ex = rmsim.run(nodes, 'main().0', R, accel=None, maxsteps=3 * 10**6)
        except RuntimeError:
            continue
        nbrute += 1
        want = spec.enum_step(s)
        got = None if ex == ('halt',) else from_regs(R)
        ok = (got == want) and (ex == ('halt',) or (ex == ('normal',) and R['scratch1'] == 0 and R['scratch2'] == 0 and R['axiomcode'] == 0))
        if not ok:
            badb += 1
            if badb < 5: print('BRUTE MISMATCH', s, ex, got, want)
    print(f'unaccelerated main runs: {nbrute}, mismatches {badb}')
    # accelerated runs, including AX with astronomically large codes
    bada = 0; kinds_seen = Counter(); stats = {}
    for t in range(ntr):
        s = rand_state(rnd, big=True)
        R = to_regs(s)
        ex = rmsim.run(nodes, 'main().0', R, accel=accel, stats=stats)
        want = spec.enum_step(s)
        got = None if ex == ('halt',) else from_regs(R)
        pl0 = s[0] - 1 if s[0] else s[1]
        ac = spec.unP(pl0)[0]
        kinds_seen['MP' if ac == 0 else 'DROP' if ac == 1 else 'NIP' if ac == 2 else 'AX'] += 1
        if want is None: kinds_seen['halt'] += 1
        ok = (got == want) and (ex == ('halt',) or (ex == ('normal',) and R['scratch1'] == 0 and R['scratch2'] == 0 and R['axiomcode'] == 0))
        if not ok:
            bada += 1
            if bada < 5: print('ACCEL MISMATCH', s, ex, want)
    print(f'accelerated main runs: {ntr}, mismatches {bada}; commands {dict(kinds_seen)}')
    print('max formula code bits seen in last state:', max(R[r].bit_length() for r in R))
    print('accelerated nodes used:', len(stats), 'of', len(accel))
    print('ALL OK' if bad == 0 and badb == 0 and bada == 0 else 'FAIL')

if __name__ == '__main__':
    main()
