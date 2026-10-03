#!/usr/bin/env python3
"""Independent, source-pinned audit of the existential congruence atom.

No repository mutation. The default root is this helper's sibling directory.
Only complete source formulas and a bounded independent census are evaluated;
the accompanying proof, not the finite census, establishes all natural fibres.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
from types import ModuleType

PINS = {
    'presburger_congruence_existence15.py': '18d66ff01e7b13b0aecd9b9c1255d4eb199d8a85df7798c96ef4c6b5df438525',
    'presburger_congruence_five.py': 'f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc',
    'presburger_congruence_existence15.json': 'd244625e6e35a57742b48844cc59b66ddfa7132b6a08fbd9e843a11bc4ebd589',
}
NAMES = ('L', 'qp', 'qm', 'b', 's', 'h')


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (tuple, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def load(data, path, name):
    # These authenticated modules have no sibling imports or decorators needing
    # registration. No temporary sys.modules entry or cache is exposed.
    mod = ModuleType(name)
    mod.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), mod.__dict__)
    return mod


def run(packet, supplied):
    env = dict(supplied)
    need(set(packet['inputs']) == set(env), 'independent executor free coordinates')
    used = set()
    for name, op, left, right in packet['gates']:
        need(type(name) is str and name not in env, 'unique gate name')
        need(op in ('add', 'sub', 'mul'), 'known operation')
        args = []
        for arg in (left, right):
            if type(arg) is int:
                args.append(arg)
            else:
                need(type(arg) is str and arg in env, 'closed ordered DAG')
                used.add(arg)
                args.append(env[arg])
        a, b = args
        env[name] = a+b if op == 'add' else a-b if op == 'sub' else a*b
    need(packet['output'] in env and all(r in env for r in packet['rows']), 'complete output')
    return env[packet['output']], tuple(env[r] for r in packet['rows'])


def ledger(packet):
    gates = packet['gates']
    live = {packet['output']}
    for name, _, a, b in reversed(gates):
        if name in live:
            live.update(v for v in (a, b) if type(v) is str)
    need(all(g[0] in live for g in gates), 'dead paid gate')
    need(set(packet['inputs']) == live.intersection(packet['inputs']), 'all input coordinates used')
    m = sum(g[1] == 'mul' for g in gates)
    return [m, len(gates)-m, len(gates)]


def outer(a, b):
    """Literal full two-atom NAND with an output=1 guard."""
    gates, rows = [], []
    inputs = ['X', 'Y']
    outputs = []
    for prefix, source, L in (('a', a, 'X'), ('b', b, 'Y')):
        rename = {'L': L}
        rename.update({n: prefix+'_'+n for n in source['inputs'] if n != 'L'})
        rename.update({g[0]: prefix+'_'+g[0] for g in source['gates']})
        inputs.extend(rename[n] for n in source['inputs'] if n != 'L')
        for n, op, x, y in source['gates']:
            gates.append([rename[n], op, rename.get(x, x), rename.get(y, y)])
        rows.extend(rename[n] for n in source['rows'])
        outputs.append(rename[source['output']])
    inputs.append('o')
    def op(kind, x, y):
        name = 'outer_'+str(len(gates))
        gates.append([name, kind, x, y])
        return name
    ta, tb = op('sub', 1, 'a_b'), op('sub', 1, 'b_b')
    nand = op('sub', 1, op('mul', ta, tb))
    relation, accept = op('sub', 'o', nand), op('sub', 'o', 1)
    output = op('add', op('add', op('add', outputs[0], outputs[1]), op('mul', relation, relation)), op('mul', accept, accept))
    return dict(inputs=inputs, gates=gates, rows=rows+[relation, accept], output=output)


def verify(root):
    import sympy as sp
    root = Path(root).resolve()
    data = {name: (root/name).read_bytes() for name in PINS}
    need({name: hashlib.sha256(value).hexdigest() for name, value in data.items()} == PINS, 'source/receipt pin mismatch')
    new = load(data['presburger_congruence_existence15.py'], root/'presburger_congruence_existence15.py', '_review_existential_congruence')
    old = load(data['presburger_congruence_five.py'], root/'presburger_congruence_five.py', '_review_canonical_congruence')
    counts = Counter()
    def check(label, condition):
        need(condition, label)
        counts[label] += 1
    symbols = dict(zip(NAMES, sp.symbols(' '.join(NAMES))))
    L, qp, qm, b, s, h = (symbols[k] for k in NAMES)
    symbolic = []
    for d in (1, 2, 11, 10**105+267):
        child, parent = new.build(d), old.build(d)
        F, rows = run(child, symbols)
        G, oldrows = run(parent, symbols)
        target = (L-d*(qp-qm)-b*(s+1), b*(s+1)+h-d+1, b*(b-1))
        for got, expected in zip(rows, target):
            check('exact_emitted_residual', sp.expand(got-expected) == 0)
        check('complete_SOS_source', sp.expand(F-sum(r*r for r in target)) == 0)
        check('full_all_value_parent_difference', sp.expand(G-F-(qp*qm)**2-((1-b)*s)**2) == 0)
        check('retained_parent_rows', all(sp.expand(rows[i]-oldrows[j]) == 0 for i, j in enumerate((1, 2, 3))))
        polynomial = sp.Poly(F, *symbols.values())
        check('exact_quartic', polynomial.total_degree() == 4 and polynomial.coeff_monomial(b*b*s*s) == 2)
        check('literal_paid_child_ledger', ledger(child) == [6, 9, 15])
        check('literal_paid_parent_ledger', ledger(parent) == [9, 12, 21])
        mixed = new.build(d, square_boolean=False)
        M, mrows = run(mixed, symbols)
        check('mixed_retained_residuals', all(sp.expand(x-y) == 0 for x, y in zip(rows, mrows)))
        check('mixed_full_output', sp.expand(M-target[0]**2-target[1]**2-target[2]) == 0)
        check('mixed_all_value_difference', sp.expand(F-M-target[2]**2+target[2]) == 0)
        check('mixed_complete_parent_difference', sp.expand(G-M-(qp*qm)**2-((1-b)*s)**2-target[2]**2+target[2]) == 0)
        check('literal_paid_mixed_ledger', ledger(mixed) == [5, 9, 14])
        mixed_poly = sp.Poly(M, *symbols.values())
        check('mixed_exact_quartic', mixed_poly.total_degree() == 4 and mixed_poly.coeff_monomial(b*b*s*s) == 2)
        symbolic.append(dict(modulus=str(d), degree=4, leading_b2s2_coefficient=2, child_ledger=[6, 9, 15], mixed_ledger=[5, 9, 14], parent_ledger=[9, 12, 21]))
    # Every tuple in the declared rectangular box is included, with no row used
    # to prefilter candidates. In particular h is an independently varied input.
    for d, number in product(range(1, 5), range(-6, 7)):
        packet = new.build(d)
        mixed = new.build(d, square_boolean=False)
        q, r = divmod(number, d)
        for p, n, bit, slack, gap in product(range(3), range(3), range(3), range(4), range(4)):
            supplied = dict(L=number, qp=p, qm=n, b=bit, s=slack, h=gap)
            expected = p-n == q and bit == int(r > 0) and gap == d-1-r and (r == 0 or slack == r-1)
            check('unfiltered_natural_box_tuples', (run(packet, supplied)[0] == 0) == expected)
            check('mixed_unfiltered_natural_box_tuples', (run(mixed, supplied)[0] == 0) == expected)
    rng = random.Random(1502026)
    for i in range(120):
        d = rng.randrange(1, 10**45)
        number = rng.randrange(-10**120, 10**120)
        if i % 3 == 0:
            number = d*rng.randrange(-10**75, 10**75)
        q, r = divmod(number, d)
        k, inactive = rng.randrange(1, 10**35), rng.randrange(1, 10**35)
        supplied = dict(L=number, qp=max(q, 0)+k, qm=max(-q, 0)+k, b=int(r > 0), s=r-1 if r else inactive, h=d-1-r)
        check('large_independent_fibre_lifts', new.evaluate(d, supplied) == 0 and 1-supplied['b'] == int(number % d == 0))
        check('mixed_large_independent_fibre_lifts', new.evaluate(d, supplied, square_boolean=False) == 0)
        check('public_witness_matches_fibre', exact(new.witness(number, d, k, inactive), supplied))
        canonical = dict(supplied, qp=max(q, 0), qm=max(-q, 0), s=max(r-1, 0))
        check('canonical_retraction', run(old.build(d), canonical)[0] == 0 and canonical['b'] == supplied['b'])
        check('strictly_larger_fibre', run(old.build(d), supplied)[0] > 0)
    # Full composed source, including both atom SOS outputs, truth expressions,
    # NAND relation, output guard, their squares and final accumulation.
    composed = outer(new.build(3), new.build(5))
    original = outer(old.build(3), old.build(5))
    mixed_outer = outer(new.build(3, square_boolean=False), new.build(5, square_boolean=False))
    check('complete_outer_ledgers', ledger(composed) == [15, 26, 41] and ledger(original) == [21, 32, 53])
    check('mixed_complete_outer_ledger', ledger(mixed_outer) == [13, 26, 39])
    env = dict(zip(composed['inputs'], sp.symbols(' '.join(composed['inputs']))))
    cv, _ = run(composed, env)
    pv, _ = run(original, env)
    correction = sum((env[p+'_qp']*env[p+'_qm'])**2+((1-env[p+'_b'])*env[p+'_s'])**2 for p in ('a', 'b'))
    check('full_composed_all_value_difference', sp.expand(pv-cv-correction) == 0)
    mv, _ = run(mixed_outer, env)
    boolean_correction = sum((env[p+'_b']*(env[p+'_b']-1))**2-env[p+'_b']*(env[p+'_b']-1) for p in ('a', 'b'))
    check('mixed_full_composed_all_value_difference', sp.expand(cv-mv-boolean_correction) == 0)
    check('mixed_full_composed_parent_difference', sp.expand(pv-mv-correction-boolean_correction) == 0)
    for x, y in product(range(-6, 7), repeat=2):
        supplied = dict(X=x, Y=y)
        for p, d, value in (('a', 3, x), ('b', 5, y)):
            q, r = divmod(value, d)
            supplied.update({p+'_qp': max(q, 0)+2, p+'_qm': max(-q, 0)+2, p+'_b': int(r > 0), p+'_s': r-1 if r else 3, p+'_h': d-1-r})
        for output in (0, 1, 2):
            supplied['o'] = output
            check('complete_outer_truth_cases', (run(composed, supplied)[0] == 0) == (output == 1 and not (x % 3 == 0 and y % 5 == 0)))
            check('mixed_complete_outer_truth_cases', (run(mixed_outer, supplied)[0] == 0) == (output == 1 and not (x % 3 == 0 and y % 5 == 0)))
    # Boundaries are affirmative counterexamples to broader, unclaimed uses.
    signed = dict(L=0, qp=0, qm=0, b=1, s=-1, h=1)
    rational = dict(L=1, qp=Fraction(1, 2), qm=0, b=0, s=0, h=1)
    privacy = dict(L=0, qp=1, qm=1, b=0, s=0, h=0)
    check('signed_domain_counterexample', run(new.build(2), signed)[0] == 0 and 1-signed['b'] != int(signed['L'] % 2 == 0))
    check('rational_domain_counterexample', run(new.build(2), rational)[0] == 0 and 1-rational['b'] != int(rational['L'] % 2 == 0))
    check('private_coordinate_export_counterexample', new.evaluate(1, privacy) == 0 and privacy['qp']*privacy['qm']-1 == 0 and run(old.build(1), privacy)[0] > 0)
    real_mixed = dict(L=1, qp=0, qm=0, b=Fraction(1, 2), s=0, h=Fraction(1, 2))
    check('mixed_nonnegative_rational_zero_not_SOS_zero', run(new.build(2, square_boolean=False), real_mixed)[0] == 0 and run(new.build(2), real_mixed)[0] == Fraction(5, 16))
    # Signed integer tuples independently supplement the unbounded B>=0 proof.
    for d in (1, 2, 7):
        sos, mixed = new.build(d), new.build(d, square_boolean=False)
        for i in range(240):
            v = {k: rng.randrange(-7, 8) for k in NAMES}
            f, rs = run(sos, v)
            m, _ = run(mixed, v)
            check('signed_complete_finalizer_zero_equivalence', (f == 0) == (m == 0) and m >= 0)
            check('signed_complete_finalizer_difference', f-m == rs[2]**2-rs[2])
    def reject(f, *args, **kwargs):
        try:
            f(*args, **kwargs)
        except ValueError:
            counts['exact_public_domain_rejections'] += 1
        else:
            raise ValueError('invalid public input accepted')
    class IntSubclass(int):
        pass
    class DictSubclass(dict):
        pass
    for bad in (True, False, 0, -1, 2.0, Fraction(2), '2', None, IntSubclass(2)):
        reject(new.build, bad)
        reject(new.witness, 1, bad)
        reject(new.evaluate, bad, dict(L=0, qp=0, qm=0, b=0, s=0, h=0))
    good = new.witness(-7, 5)
    for n in NAMES:
        for bad in (True, 1.0, Fraction(1), None, IntSubclass(1)):
            reject(new.evaluate, 5, dict(good, **{n: bad}))
        if n != 'L':
            reject(new.evaluate, 5, dict(good, **{n: -1}))
    for bad in (None, [], DictSubclass(good), {**good, 'extra': 0}, {n: v for n, v in good.items() if n != 'h'}):
        reject(new.evaluate, 5, bad)
    for bad in (True, 1.0, Fraction(1), None, IntSubclass(1)):
        reject(new.witness, bad, 5)
    for key in ('shift', 'inactive_slack'):
        for bad in (-1, True, 1.0, Fraction(1), None, IntSubclass(1)):
            reject(new.witness, -7, 5, **{key: bad})
    for bad in (0, 1, 0.0, 1.0, Fraction(1), None, 'False', []):
        reject(new.build, 5, square_boolean=bad)
        reject(new.evaluate, 5, good, square_boolean=bad)
    packet = new.build(7)
    baseline = new.build(7)
    packet['gates'][-1][1] = 'sub'
    packet['inputs'][0] = 'forged'
    check('build_has_no_public_mutable_cache', exact(new.build(7), baseline))
    author = subprocess.run([sys.executable, str(root/'presburger_congruence_existence15.py'), '--parent', str(root/'presburger_congruence_five.py'), '--expect', str(root/'presburger_congruence_existence15.json')], check=True, capture_output=True, text=True, timeout=60)
    author_summary = json.loads(author.stdout)
    check('fresh_author_saved_receipt', exact(author_summary, {'checks': 56593, 'status': 'PASS_EXISTENTIAL_CONGRUENCE_15_AND_14'}))
    return dict(status='PASS_INDEPENDENT_EXISTENTIAL_CONGRUENCE_15_AND_14', pins=PINS, counts=dict(counts), symbolic_records=symbolic,
                author_replay=author_summary,
                outer_NAND=dict(new_ledger=[15, 26, 41], mixed_ledger=[13, 26, 39], parent_ledger=[21, 32, 53], natural_auxiliaries=11, residuals=8, complete_new_source=composed, complete_mixed_source=mixed_outer),
                domain_and_privacy_examples=dict(signed_integer=signed, nonnegative_rational={k: str(v) for k, v in rational.items()}, forbidden_private_read=privacy, mixed_real_zero={k: str(v) for k, v in real_mixed.items()}),
                scope='Same congruence truth over five natural witnesses for every signed integer L and fixed exact positive integer d; infinite fibres, truth-only composition. Complete atoms 15=6M+9A and 14=5M+9A have the same integer zeros, not the same real zeros; costs exclude L evaluation and truth expression/outer work. Full NAND example pays those outer gates. No canonical-fibre bijection, minimum circuit or fixed-arity universal improvement.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--expect', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.root)
    if args.expect:
        need(exact(result, json.loads(args.expect.read_text())), 'independent receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': result['status'], 'counts': result['counts']}, sort_keys=True))
