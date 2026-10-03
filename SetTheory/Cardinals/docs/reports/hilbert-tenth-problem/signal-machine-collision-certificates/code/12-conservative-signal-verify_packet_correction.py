#!/usr/bin/env python3
"""Independent boundary regressions and literal-formula preservation checks.

Usage: python verify_packet_correction.py NEW_MODULE [--original OLD_MODULE]
The evaluator's expected domain is exact nonnegative builtin integers.
"""
import argparse
import importlib.util
import json
import random
import sys
from pathlib import Path


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def formula(branches, x, y, witness):
    selectors, copies, slacks = witness
    d = len(x)
    rows = [sum(selectors) - 1]
    rows += [x[i] - sum(copy[i] for copy in copies) for i in range(d)]
    rows += [y[i] - sum(sum(branch.matrix[i][j] * copies[r][j]
              for j in range(d)) for r, branch in enumerate(branches))
              for i in range(d)]
    for r, branch in enumerate(branches):
        slack_index = 0
        for guard in branch.guards:
            value = sum(guard.coeff[i] * copies[r][i] for i in range(d))
            if guard.kind != 'eq':
                value -= slacks[r][slack_index]
                if guard.kind == 'gt':
                    value -= selectors[r]
                slack_index += 1
            rows.append(value)
    products = tuple(sum(selectors[s] for s in range(len(branches)) if s != r)
                     * sum(copies[r]) for r in range(len(branches)))
    return tuple(rows), products


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repaired', type=Path)
    parser.add_argument('--original', type=Path)
    args = parser.parse_args()
    new = load(args.repaired, 'packet_new')
    old = load(args.original, 'packet_old') if args.original else None
    modules = ([('original', old)] if old is not None else []) + [('repaired', new)]
    findings = {}
    for module_name, module in modules:
        branch = (module.Branch(((1,),), ()),)
        w = module.canonical_witness(branch, (1,), (1,))
        cases = {
            'surplus_output': lambda: module.polynomial_value(branch, (1,), (1, 999), w),
            'floating_source': lambda: module.polynomial_value(branch, (1.0,), (1,), w),
            'surplus_none_slack': lambda: module.polynomial_value(branch, (1,), (1,), (w[0], w[1], ((None,),))),
        }
        findings[module_name] = {}
        for label, call in cases.items():
            try:
                value = call()
            except (ValueError, TypeError) as error:
                findings[module_name][label] = type(error).__name__
                require(module is new, label + ' not reproduced in original')
            else:
                findings[module_name][label] = value
                require(module is old and value == 0, label + ' accepted by repaired module')

    rng = random.Random(2026100223)
    preserved = 0
    for d in range(1, 7):
        for count in range(5):
            raw = [(tuple(tuple(rng.randrange(-3, 4) for _ in range(d)) for _ in range(d)),
                    [(kind, tuple(rng.randrange(-3, 4) for _ in range(d)))
                     for kind in ('ge', 'eq', 'gt', 'eq', 'ge')]) for _ in range(count)]
            pairs = [(m, tuple(m.Branch(matrix, tuple(m.Guard(k, v) for k, v in guards))
                               for matrix, guards in raw)) for _, m in modules]
            bs_new = pairs[-1][1]
            for _ in range(40):
                x, y = [tuple(rng.randrange(8) for _ in range(d)) for _ in range(2)]
                w = (tuple(rng.randrange(4) for _ in range(count)),
                     tuple(tuple(rng.randrange(8) for _ in range(d)) for _ in range(count)),
                     tuple(tuple(rng.randrange(8) for _ in range(3)) for _ in range(count)))
                expected = formula(bs_new, x, y, w)
                for m, bs in pairs:
                    require(m.packet_terms(bs, x, y, w) == expected, 'Literal residual mismatch')
                    require(m.polynomial_value(bs, x, y, w) == sum(v*v for v in expected[0]) + sum(expected[1]), 'Literal polynomial mismatch')
                preserved += 1

    rejections = 0
    def reject(call):
        nonlocal rejections
        try:
            call()
        except (ValueError, TypeError):
            rejections += 1
        else:
            raise AssertionError('Malformed call was accepted')
    branch = (new.Branch(((1, 0), (0, 1)), (new.Guard('gt', (1, 0)),)),)
    x = (1, 2)
    w = new.canonical_witness(branch, x, x)
    for bad in [(), (1,), (1, 2, 0), (1.0, 2), (True, 2), (-1, 2), ('1', 2), (None, 2)]:
        reject(lambda: new.canonical_witness(branch, bad, x))
        reject(lambda: new.canonical_witness(branch, x, bad))
        reject(lambda: new.polynomial_value(branch, bad, x, w))
        reject(lambda: new.polynomial_value(branch, x, bad, w))
    for sels in [(), (True,), (1.0,), (-1,), (1, 0)]:
        reject(lambda: new.polynomial_value(branch, x, x, (sels, w[1], w[2])))
    for copies in [(), ((1,),), ((1, 2, 0),), ((True, 2),), ((1.0, 2),), ((-1, 2),)]:
        reject(lambda: new.polynomial_value(branch, x, x, (w[0], copies, w[2])))
    for slacks in [(), ((),), ((0, None),), ((True,),), ((0.0,),), ((-1,),), ((0,), ())]:
        reject(lambda: new.polynomial_value(branch, x, x, (w[0], w[1], slacks)))
    for matrix in [(), ((1, 2),), ((True,),), ((1.0,),), ((None,),)]:
        reject(lambda: new.Branch(matrix, ()))
    for coeff in [(True,), (1.0,), (None,)]:
        reject(lambda: new.Guard('eq', coeff))
    for kind in ['bad', '', None]:
        reject(lambda: new.Guard(kind, (1,)))
    reject(lambda: new.Branch(((1,),), (new.Guard('eq', (1, 2)),)))
    reject(lambda: new.Branch(((1,),), ('bad',)))
    reject(lambda: new.Branch(((1,),), ()).output((1, 2)))
    reject(lambda: new.Guard('eq', (1,)).value((1, 2)))

    canonical = 0
    for d in range(1, 7):
        ident = tuple(tuple(int(i == j) for j in range(d)) for i in range(d))
        axis = (1,) + (0,) * (d - 1)
        pairs = [tuple([m.Branch(ident, (m.Guard('eq', axis),)),
                       m.Branch(ident, (m.Guard('gt', axis), m.Guard('ge', axis)))])
                 for _, m in modules]
        for n in range(12):
            x = (n,) * d
            ws = [m.canonical_witness(bs, x, x) for (_, m), bs in zip(modules, pairs)]
            require(all(w == ws[-1] for w in ws) and ws[-1] is not None, 'Canonical witness changed')
            require(new.polynomial_value(pairs[-1], x, x, ws[-1]) == 0, 'Canonical witness invalid')
            canonical += 1
    overlap = (new.Branch(((1,),), ()), new.Branch(((1,),), ()))
    reject(lambda: new.canonical_witness(overlap, (1,), (1,)))
    matrix, coeff, mode, ties = [[1]], [1], ['a'], [0]
    guards = [new.Guard('ge', coeff)]
    b = new.Branch(matrix, guards, mode, ties)
    matrix[0][0] = 3
    coeff[0] = 7
    guards.clear()
    mode.clear()
    ties.clear()
    require(b.matrix == ((1,),) and b.guards[0].coeff == (1,) and b.mode == ('a',) and b.tied_edges == (0,), 'Mutable snapshot retained')
    require(new.Branch(((-2,),), ()).output((-3,)) == (6,), 'Signed algebraic method changed')
    print(json.dumps({'status':'PASS', 'regressions':findings, 'complete_formula_preservation_cases':preserved,
                      'canonical_sections_preserved':canonical, 'malformed_calls_rejected':rejections,
                      'immutable_snapshot_verified':True, 'signed_branch_algebra_preserved':True,
                      'python_assertions_enabled':__debug__, 'original_code_compared':old is not None}, indent=2))


if __name__ == '__main__':
    main()
