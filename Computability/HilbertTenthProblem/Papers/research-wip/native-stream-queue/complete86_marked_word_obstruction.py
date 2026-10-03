"""Literal 83-gate marked-word shortcut and its input-width obstruction.

The note proves a full counterfamily by transporting canonical parent zeros.
This helper checks complete source identities and bounded supporting components.
"""
import argparse, hashlib, json, random
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without -O')

PINS = {
    'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
    'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
    'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
    'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
    'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
    '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def atom(v):
    return {(v,): 1} if type(v) is str else ({(): v} if v else {})

def add(a, b, sign=1):
    out = dict(a)
    for mon, coefficient in b.items():
        out[mon] = out.get(mon, 0) + sign * coefficient
    return {m: c for m, c in out.items() if c}

def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(sorted(ma + mb))
            out[m] = out.get(m, 0) + ca * cb
    return {m: c for m, c in out.items() if c}

def evaluate(rows, assignment):
    env = dict(assignment)
    for name, op, a, b in rows:
        a = env[a] if type(a) is str else a
        b = env[b] if type(b) is str else b
        env[name] = a * b if op == '*' else a + b if op == '+' else a - b
    return env

def inspect(rows, free):
    seen = set(free)
    definitions = {}
    for name, op, a, b in rows:
        need(name not in seen and op in ('+', '-', '*'), 'Fresh arithmetic gate')
        need(all(type(v) is int or type(v) is str and v in seen for v in (a, b)), 'Closed literal source')
        seen.add(name)
        definitions[name] = (a, b)
    live = set()
    stack = ['polynomial']
    while stack:
        name = stack.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        stack.extend(definitions.get(name, ()))
    need(seen <= live, 'All source gates and supplied ports live')
    products = sum(row[1] == '*' for row in rows)
    return dict(M=products, A=len(rows)-products, operations=len(rows), all_live=True)

def pell(A, n):
    c0, c1, s0, s1 = 1, A, 0, 1
    if n == 0:
        return c0, s0
    for _ in range(1, n):
        c0, c1 = c1, 2*A*c1-c0
        s0, s1 = s1, 2*A*s1-s0
    return c1, s1

def verify(root):
    root = Path(root)
    for name, pin in PINS.items():
        need(hashlib.sha256((root/name).read_bytes()).hexdigest() == pin, 'Pinned predecessor '+name)
    parent = json.loads((root/'complete86_factored_first_root.json').read_text())['forms'][0]
    need(parent['normalized'] is True, 'Actual normalized parent')
    old = parent['source']
    defs = {r[0]: r[1:] for r in old}
    need([r[0] for r in old if 'alpha' in r[2:]] == ['C_after_alpha'], 'Private alpha coordinate')
    need([r[0] for r in old if 'C_after_alpha' in r[2:]] == ['marked_rhs'], 'Private bound chain')
    need([r[0] for r in old if 'q_minus_FZ' in r[2:]] == ['C_after_alpha', 'gap'], 'Exact shared gap consumers')
    for name, row in {
        'q_minus_FZ': ['-', 'q_minus_F', 'Z'],
        'C_after_alpha': ['-', 'q_minus_FZ', 'alpha'],
        'scaled_t': ['*', 'twice_cell_bits', 'x'],
        'marked_rhs': ['-', 'C_after_alpha', 'scaled_t'],
        'gap_product': ['*', 'repunit', 'q_minus_F'],
        'gap': ['+', 'gap_product', 'q_minus_FZ'],
        'q': ['+', 'repunit', 1],
    }.items():
        need(defs[name] == row, 'Actual source cut '+name)
    witnesses = ['C_word' if x == 'alpha' else x for x in parent['witnesses']]
    free = witnesses + ['x'] + parent['ledger']['fixed_numerals']
    intermediate = [[n, op, 'C_word' if a == 'marked_rhs' else a, 'C_word' if b == 'marked_rhs' else b]
                    for n, op, a, b in old if n not in ('C_after_alpha', 'marked_rhs')]
    rows = []
    for n, op, a, b in intermediate:
        if n == 'q_minus_FZ':
            continue
        if n == 'gap_product':
            a = 'q'
        elif n == 'gap':
            op, b = '-', 'Z'
        rows.append([n, op, a, b])
    ledgers = [inspect(s, free) for s in (intermediate, rows)]
    need([(p['M'], p['A']) for p in ledgers] == [(48, 36), (48, 35)], 'Complete84/83 ledgers')
    q, F, Z, ell, C = [atom(v) for v in ('q', 'F', 'Z', 'ell', 'C')]
    bound = add(add(add(add(q, F, -1), Z, -1), ell, -1), C, -1)
    reconstructed = add(add(add(add(q, F, -1), Z, -1), bound, -1), ell, -1)
    need(reconstructed == C, 'Exact bound-coordinate inverse cut')
    u = add(q, F, -1)
    need(add(mul(add(q, atom(1), -1), u), add(u, Z, -1)) == add(mul(q, u), Z, -1), 'Exact paid gap cut')
    # Both cut identities plus the literal retained rows prove the full pullback.
    rng = random.Random(860083)
    comparisons = 0
    for case in range(48):
        child = {n: rng.randrange(1, 6) for n in free}
        child.update(Bm1=15, Kconstant=83, twice_cell_bits=8, inner_bits=3, MC=14, MF=19)
        if case >= 24:
            child = {n: Fraction(v, 3) for n, v in child.items()}
        restored = {n: v for n, v in child.items() if n != 'C_word'}
        restored['alpha'] = child['Bm1']*child['Jrep']+1-child['F']-child['Z']-child['twice_cell_bits']*child['x']-child['C_word']
        before = evaluate(old, restored)
        for candidate in (intermediate, rows):
            after = evaluate(candidate, child)
            need(all(before[n] == after[n] for n in after if n in before and n != 'gap_product'), 'Whole-source signed graph comparison')
            need(before['marked_rhs'] == child['C_word'], 'Restored complete marked word')
            comparisons += 1
    # An exact transport identity, independent of any zero assumptions.
    K, X, W, z = [atom(v) for v in ('K', 'X', 'W', 'z')]
    oldC = add(Z, W)
    newC = add(Z, mul(mul(q, q), W))
    znew = add(z, mul(mul(add(K, X), add(q, atom(1))), W))
    def transport(cc, zz):
        return add(add(mul(add(K, X), cc), add(q, F, -1)), mul(zz, add(q, atom(1), -1)), -1)
    need(transport(oldC, z) == transport(newC, znew), 'Exact entire transport compensation')
    inputs = []
    for A, R, e, t in [(3,63,11,12), (7,95,13,16), (17,127,17,24), (41,159,19,28)]:
        need(e % 2 == 1 and 3 <= e < t and e+2*t < R, 'Independent input component indices')
        a, Delta, H = A-2, A*A-1, 4*A-5
        main, c = pell(A, R)
        gamma, rem = divmod(main-a*c-2**R, H)
        need(rem == 0, 'Main projection recurrence')
        data = []
        for exponent in (e, e+2*t):
            mu, kappa = pell(A, exponent)
            delta, rem = divmod(kappa-exponent, Delta)
            rho, rem2 = divmod(mu-a*kappa-2**exponent, H)
            sigma = gamma-rho
            need(rem == rem2 == 0 and min(delta,rho,sigma) > 0, 'Positive input quotients and split')
            need((2**exponent+a*(exponent+delta*Delta)+rho*H)**2-Delta*(exponent+delta*Delta)**2 == 1, 'Actual input factor')
            need(2**R+a*c+(rho+sigma)*H == main, 'Actual shared main root unchanged')
            data.append(dict(exponent=exponent, input_coefficient_bits=kappa.bit_length(), positive_quotients=True))
        need(2**(e+2*t) == (2**t)**2*2**e, 'Whole-cell input shift')
        inputs.append(dict(A=A,R=R,t=t,inputs=data,scope='Pell input/main-root components only; not full compiler-width zeros.'))
    return dict(status='PASS_MARKED_WORD_SOURCE_AND_INPUT_WIDTH_OBSTRUCTION',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pins=PINS,witnesses=witnesses,free=free,forms=[dict(source=s,ledger=l) for s,l in zip((intermediate,rows),ledgers)],counts=dict(exact_cut_identities=2,whole_source_graph_comparisons=comparisons,exact_transport_identities=1,input_shift_components=len(inputs)),input_components=inputs,scope='General proof transports canonical complete positive parent zeros to complete positive child zeros at x+N. Finite checks certify source pullbacks and supporting components, not a materialized full compiler witness. Neither84 nor83 is a certified universal bound.')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    args = parser.parse_args()
    result = verify(args.root)
    if args.expect:
        need(exact(result,json.loads(args.expect.read_text())), 'Exact typed receipt')
    if args.output:
        args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(result['status'],result['counts'])

if __name__ == '__main__':
    main()
