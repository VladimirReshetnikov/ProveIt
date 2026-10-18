"""Prototype symbolic run-length executor for zfc_254.tm (design model for the Coq checker).

Config (q, form, L, R): form 'c' = head on R[0], 'l' = head on L[0]; L is read leftwards.
Segments: ('b', x) one cell; ('r', b, a, c) run of a*n+c cells of b (n = free gap parameter);
('box', st) the register file sepsR(vs) (only as last segment of R; its first cell is 0).
Box oracles (validated by boxcheck.py, to be proved generically in Coq):
  skip state S_j at box start, plain box   -> mark block j+1, exit zl (2 if j=-1 else 6)
  73 at box start, box marked r            -> inc r, exit zl 48
  43 at box start, box marked r            -> zero: exit zl 3 plain; pos: dec r (+[0]), exit zl (63 if r=0 else 48)
"""
import sys, json; sys.path.insert(0, '.')
from tmlib import load
from collections import Counter
T, _ = load(sys.argv[1]); D = sys.argv[2]; D0 = int(sys.argv[3])
SKIP = {'69': 7, '64': 6, '28': 5, '40': 4, '38': 3, '56': 2, '31': 1, '44': 0, '60': -1}
REG = dict(wffstack=0, param1=1, axiomcode=2, scratch2=3, scratch1=4, prooflist=5, nextproof=6, topwff=7, param2=8)

class Fail(Exception): pass

def run(q, L, R, branch, expect, fuel=20000):
    form = 'c'; box_eff = []; steps = 0; visits = 0
    while fuel > 0:
        fuel -= 1
        if q == '254':
            return ('halt', steps, visits)
        if form == 'c' and q == '96':
            visits += 1
            if steps > 0 and canon(L, R) == expect:
                return ('ok', steps, visits)
        if form == 'l':
            if not L:
                R = [('b', 0)] + R; form = 'c'; continue
            s = L[0]
            if s[0] == 'b':
                L = L[1:]; R = [s] + R; form = 'c'; continue
            _, b, a, c = s
            w, d, q2 = T[(q, b)]
            if d == 'L' and q2 == q:
                L = L[1:]; R = [('r', w, a, c)] + R; steps += 1; continue
            if c >= 1:
                L = ([('r', b, a, c - 1)] if (a, c - 1) != (0, 0) else []) + L[1:]
                R = [('b', b)] + R; form = 'c'; continue
            if a == 0:
                L = L[1:]; continue
            raise Fail('peel left symbolic run in %s' % q)
        # form c
        if not R: raise Fail('right exterior')
        s = R[0]
        if s[0] == 'b':
            w, d, q2 = T[(q, s[1])]; steps += 1
            if d == 'R': L = [('b', w)] + L; R = R[1:]
            else: R = [('b', w)] + R[1:]; form = 'l'
            q = q2; continue
        if s[0] == 'r':
            _, b, a, c = s
            w, d, q2 = T[(q, b)]
            if d == 'R' and q2 == q:
                L = [('r', w, a, c)] + L; R = R[1:]; steps += 1; continue
            if c >= 1:
                R = [('b', b)] + ([('r', b, a, c - 1)] if (a, c - 1) != (0, 0) else []) + R[1:]; continue
            if a == 0:
                R = R[1:]; continue
            raise Fail('peel right symbolic run in %s' % q)
        # box
        st = s[1]
        if q in SKIP and st[0] == 'plain':
            r = SKIP[q] + 1; R = [('box', ('mark', r) + st[1:])]
            q = '2' if r == 0 else '6'; form = 'l'; steps += 1; continue
        if q == '73' and st[0] == 'mark':
            r = st[1]; R = [('box', ('plain',) + st[2:] + (('inc', r),))]
            q = '48'; form = 'l'; steps += 1; continue
        if q == '43' and st[0] == 'mark':
            r = st[1]
            if branch == 'z': R = [('box', ('plain',) + st[2:] + (('dec0', r),))]; q = '3'
            else: R = [('box', ('plain',) + st[2:] + (('dec', r),))]; q = '63' if r == 0 else '48'
            form = 'l'; steps += 1; continue
        w, d, q2 = T[(q, 0)]
        if w == 0 and d == 'L':
            q = q2; form = 'l'; steps += 1; continue
        raise Fail('box touched in state %s' % q)
    raise Fail('fuel')

def canon_side(segs, left):
    out = []
    for s in segs:
        if s[0] == 'box': out.append(('box', s[1])); continue
        b, a, c = (s[1], 0, 1) if s[0] == 'b' else s[1:]
        if (a, c) == (0, 0): continue
        if out and out[-1][0] == b: out[-1] = (b, out[-1][1] + a, out[-1][2] + c)
        else: out.append((b, a, c))
    if left:
        while out and out[-1][0] == 0: out.pop()
    return tuple(out)
def canon(L, R): return (canon_side(L, True), canon_side(R, False))

def inc(P):
    if '0' not in P: return None
    j = P.rindex('0'); return P[:j] + '1'
def strip(b, k, P):
    while k > 0:
        if not P: return ''
        if P[-1] == b: k -= 1
        P = P[:-1]
    return P
def cells(P): return [('b', int(x)) for x in P]
def tape_R(P, extra, eff):
    return cells(P) + [('r', 0, 1, D0 + extra - len(P)), ('b', 1), ('box', ('plain',) + eff)]

paths = json.load(open(D + '/paths.json'))
res = Counter(); worst = Counter()
for i, (p, op) in enumerate(paths):
    Q = p[3:]
    if op == 'halt': cases = [('-', None)]
    elif op.endswith('.decnz'): cases = [('z', 'dec0'), ('p', 'dec')]
    else: cases = [('-', 'inc' if op.endswith('.inc') else None)]
    for br, eff in cases:
        if op.endswith('.inc') or (op.endswith('.decnz') and br == 'p'): Q2 = inc(Q)
        elif op.endswith('.decnz'): Q2 = inc(strip('0', 1, Q))
        elif op.startswith('_continue'): Q2 = strip('1', int(op.split('.')[1]), Q)
        elif op.startswith('_break'): Q2 = inc(strip('0', int(op.split('.')[1]), Q))
        else: Q2 = ''
        e = () if eff is None else ((eff, REG[op.split('.')[1]]),)
        if Q2 is None: exp = canon([('b', 1)], [('r', 0, 1, D0 + 1), ('b', 1), ('box', ('plain',) + e)]); tag = 'overflow'
        else: exp = canon([('b', 1)], tape_R(Q2, 0, e)); tag = 'normal'
        try:
            out = run('96', [('b', 1)], tape_R(Q, 0, ()), br, exp)
        except Fail as f:
            res['FAIL ' + str(f)] += 1
            if res['FAIL ' + str(f)] <= 3: print('fail site', i, p, op, br, f)
            continue
        if op == 'halt':
            res['halt' if out[0] == 'halt' else 'BAD halt'] += 1
        else:
            res[out[0] + ' ' + tag] += 1
            worst['maxsteps'] = max(worst['maxsteps'], out[1]); worst['maxvisits'] = max(worst['maxvisits'], out[2])
            worst['steps_total'] += out[1]
print('D0 =', D0, dict(res), dict(worst))
