#!/usr/bin/env python3
"""Existential congruence: fifteen SOS gates or fourteen with an integer guard.

Fixed d>=1; L is an already evaluated signed integer affine input.
Only 1-b is exported. All other atom coordinates must remain private.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random

PARENT_SHA = 'f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc'
NAMES = ('L', 'qp', 'qm', 'b', 's', 'h')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def modulus(d):
    require(type(d) is int and d >= 1, 'fixed modulus must be an exact positive integer')
    return d


def build(d, *, square_boolean=True):
    modulus(d)
    require(type(square_boolean) is bool, 'square_boolean must be an exact Boolean')
    gates = []
    def op(kind, a, b):
        name = 'g' + str(len(gates))
        gates.append([name, kind, a, b])
        return name
    bs = op('mul', 'b', 's')
    r = op('add', bs, 'b')
    q = op('sub', 'qp', 'qm')
    dq = op('mul', d, q)
    quotient = op('sub', op('sub', 'L', dq), r)
    bound = op('sub', op('add', r, 'h'), d-1)
    boolean = op('mul', 'b', op('sub', 'b', 1))
    rows = [quotient, bound, boolean]
    squares = [op('mul', row, row) for row in rows[:2]]
    squares.append(op('mul', boolean, boolean) if square_boolean else boolean)
    output = op('add', op('add', squares[0], squares[1]), squares[2])
    return dict(modulus=d, inputs=list(NAMES), gates=gates, rows=rows,
                output=output, square_boolean=square_boolean,
                multiplications=5+int(square_boolean), additions=9, operations=14+int(square_boolean))


def _execute(packet, inputs):
    env = dict(inputs)
    def value(ref):
        return ref if type(ref) is int else env[ref]
    for name, kind, a, b in packet['gates']:
        a, b = value(a), value(b)
        env[name] = a*b if kind == 'mul' else a+b if kind == 'add' else a-b
    return env[packet['output']], tuple(env[row] for row in packet['rows'])


def evaluate(d, inputs, *, square_boolean=True):
    modulus(d)
    require(type(inputs) is dict and set(inputs) == set(NAMES), 'exact input names required')
    require(all(type(inputs[n]) is int for n in NAMES), 'exact integer inputs required')
    require(all(inputs[n] >= 0 for n in NAMES if n != 'L'), 'natural witnesses required')
    return _execute(build(d, square_boolean=square_boolean), inputs)[0]


def witness(L, d, shift=0, inactive_slack=0):
    modulus(d)
    require(type(L) is int, 'signed integer input required')
    require(type(shift) is int and shift >= 0, 'natural quotient shift required')
    require(type(inactive_slack) is int and inactive_slack >= 0, 'natural inactive slack required')
    q, r = divmod(L, d)
    return dict(L=L, qp=max(q, 0)+shift, qm=max(-q, 0)+shift,
                b=int(r != 0), s=r-1 if r else inactive_slack, h=d-1-r)


def _parent(path):
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == PARENT_SHA, 'parent source pin mismatch')
    spec = importlib.util.spec_from_file_location('_pinned_congruence_parent', path)
    mod = importlib.util.module_from_spec(spec)
    exec(compile(data, str(path), 'exec'), mod.__dict__)
    return mod


def verify(parent):
    import sympy as sp
    old = _parent(parent)
    counts = {}
    def check(label, ok):
        require(ok, label)
        counts[label] = counts.get(label, 0)+1
    symbols = dict(zip(NAMES, sp.symbols(' '.join(NAMES))))
    L, qp, qm, b, s, h = (symbols[n] for n in NAMES)
    for d in (1, 2, 7, 10**50+3):
        packet = build(d)
        value, rows = _execute(packet, symbols)
        parent_value, parent_rows = old.evaluate(old.build(d), symbols)
        expected = [L-d*(qp-qm)-b*(s+1), b*(s+1)+h-d+1, b*(b-1)]
        check('complete_symbolic_residuals', all(sp.expand(x-y) == 0 for x, y in zip(rows, expected)))
        check('full_parent_difference_identity', sp.expand(parent_value-value-(qp*qm)**2-((b-1)*s)**2) == 0)
        check('exact_degree_four', sp.Poly(value, *symbols.values()).total_degree() == 4)
        check('charged_literal_gates', len(packet['gates']) == 15 and sum(g[1] == 'mul' for g in packet['gates']) == 6 and sum(g[1] != 'mul' for g in packet['gates']) == 9)
        live = {packet['output']}
        for name, kind, left, right in reversed(packet['gates']):
            if name in live:
                live.update(x for x in (left, right) if type(x) is str)
        check('all_paid_gates_live', all(g[0] in live for g in packet['gates']))
        mixed = build(d, square_boolean=False)
        mixed_value, mixed_rows = _execute(mixed, symbols)
        check('mixed_same_residuals', rows == mixed_rows)
        check('mixed_complete_difference_identity', sp.expand(value-mixed_value-(b*(b-1))**2+b*(b-1)) == 0)
        check('mixed_exact_degree_four', sp.Poly(mixed_value, *symbols.values()).total_degree() == 4)
        check('mixed_charged_gates', len(mixed['gates']) == 14 and sum(g[1] == 'mul' for g in mixed['gates']) == 5 and sum(g[1] != 'mul' for g in mixed['gates']) == 9)
    # Complete bounded fibres: independent Euclidean characterization, including
    # non-Boolean candidates, noncanonical quotient shifts and inactive slacks.
    for d in range(1, 7):
        for number in range(-9, 10):
            q, r = divmod(number, d)
            for p, n, bit, slack in itertools.product(range(5), range(5), range(4), range(d+2)):
                rest = d-1-bit*(slack+1)
                if rest < 0:
                    continue
                inp = dict(L=number, qp=p, qm=n, b=bit, s=slack, h=rest)
                expected = p-n == q and bit == int(r != 0) and (r == 0 or slack == r-1) and rest == d-1-r
                check('bounded_fibre_characterization', (evaluate(d, inp) == 0) == expected)
                check('mixed_bounded_fibre_characterization', (evaluate(d, inp, square_boolean=False) == 0) == expected)
    rng = random.Random(150621)
    for _ in range(400):
        number = rng.randrange(-10**60, 10**60)
        d = rng.randrange(1, 10**20)
        inp = witness(number, d, shift=rng.randrange(1, 10**8), inactive_slack=rng.randrange(10**8))
        check('large_shifted_natural_zeros', evaluate(d, inp) == 0 and 1-inp['b'] == int(number % d == 0))
        check('canonical_parent_section', old.evaluate(old.build(d), witness(number, d))[0] == 0)
        check('larger_fibre_than_parent', old.evaluate(old.build(d), inp)[0] > 0)
    # Divisible inputs exercise the unrestricted inactive slack, also at d=1.
    for d, quotient, shift, slack in itertools.product(range(1, 6), range(-3, 4), range(4), range(4)):
        inp = witness(d*quotient, d, shift, slack)
        check('divisible_inactive_fibres', evaluate(d, inp) == 0 and inp['b'] == 0)
    # An outer circuit reads only the two atom truth outputs. Its final guard
    # accepts NAND, with all atom internals still private and arbitrarily shifted.
    for x, y in itertools.product(range(-8, 9), repeat=2):
        a, b = witness(x, 3, 4, 7), witness(y, 5, 6, 9)
        expected = not (x % 3 == 0 and y % 5 == 0)
        for output in (0, 1):
            gate = output-(1-(1-a['b'])*(1-b['b']))
            full = evaluate(3, a)+evaluate(5, b)+gate*gate+(output-1)**2
            check('complete_outer_NAND_acceptance', (full == 0) == (bool(output) and expected))
    for bad in (True, 0, -1, 2.0, None):
        try:
            build(bad)
        except ValueError:
            check('invalid_modulus_rejected', True)
        else:
            raise AssertionError('invalid modulus accepted')
    for bad in (0, 1, 0.5, None):
        try:
            build(7, square_boolean=bad)
        except ValueError:
            check('invalid_mode_rejected', True)
        else:
            raise AssertionError('invalid mode accepted')
    # Nonnegativity of the unsquared Boolean product requires integrality.
    # This complete real zero of the mixed polynomial has Boolean residual -1/4.
    real = dict(L=0, qp=0, qm=sp.Rational(1, 2), b=sp.Rational(1, 2), s=0, h=0)
    check('complete_real_domain_counterexample', _execute(build(1, square_boolean=False), real)[0] == 0 and _execute(build(1), real)[0] == sp.Rational(5, 16))
    for bit in range(-20, 21):
        check('integer_boolean_product_nonnegative', bit*(bit-1) >= 0 and ((bit*(bit-1) == 0) == (bit in (0, 1))))
    good = witness(-12, 7)
    for key in NAMES:
        for bad in (True, 1.0, None):
            inp = dict(good, **{key: bad})
            try:
                evaluate(7, inp)
            except ValueError:
                check('inexact_input_rejected', True)
            else:
                raise AssertionError('inexact input accepted')
    return dict(status='PASS_EXISTENTIAL_CONGRUENCE_15_AND_14', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                parent_sha256=PARENT_SHA, counts=counts, total_checks=sum(counts.values()),
                schedule=build(7), mixed_schedule=build(7, square_boolean=False), witnesses=5, residuals=3, exact_degree=4,
                compiler_witnesses='2I+5C+G', compiler_residuals='2I+3C+G+1',
                scope='Same existential congruence truth for every signed integer L and fixed d>=1. Every input has infinitely many natural internal witnesses. Only 1-b may be exported; no canonical-fibre or all-value equality to the parent is claimed. The fourteen-gate variant has the same integer zero set as the fifteen-gate SOS, but not the same real zero set. L evaluation, Boolean gates and final accumulation are separate; no universal bound improvement.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--parent', type=Path, default=Path(__file__).with_name('presburger_congruence_five.py'))
    p.add_argument('--output', type=Path)
    p.add_argument('--expect', type=Path)
    args = p.parse_args()
    result = verify(args.parent)
    if args.expect:
        require(json.dumps(result, sort_keys=True) == json.dumps(json.loads(args.expect.read_text()), sort_keys=True), 'saved receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(status=result['status'], checks=result['total_checks']), sort_keys=True))
