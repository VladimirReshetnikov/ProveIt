#!/usr/bin/env python3
"""Read JSON data only; never import or execute the author's emitter.

Independent exponent-vector polynomial expansion, gadget reconstruction,
complete finite logic truth tables, and exact integer evaluation regressions.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

PIN = '51753ea012b966f3a0c16c4dbf8f9766f67bfa9c66afd56134047c469834a1bc'
EXPORT_PINS = {
    'four_signal_quartic.json': '79f81249129b5329a8cfec998363e9c69602b23b6b3f12a27284f0a4cb9237c6',
    'quadratic_sign_quartic.json': 'bf3c2978ab36acfc9c87327f687282e4550a214039ca20036fadf94abebd685e',
}


def unique_object(pairs):
    d = {}
    for k, v in pairs:
        assert k not in d, ('duplicate JSON key', k)
        d[k] = v
    return d


class Algebra:
    def __init__(self, names):
        self.names = tuple(names)
        assert len(set(self.names)) == len(self.names)
        self.index = {v: i for i, v in enumerate(self.names)}
        self.zero = (0,) * len(self.names)

    def constant(self, n):
        return {self.zero: n} if n else {}

    def variable(self, name):
        exponents = list(self.zero)
        exponents[self.index[name]] = 1
        return {tuple(exponents): 1}

    def add(self, *polys):
        c = Counter()
        for p in polys:
            for m, value in p.items():
                c[m] += value
        return {m: value for m, value in c.items() if value}

    def scale(self, p, n):
        return {m: value * n for m, value in p.items() if value * n}

    def product(self, p, q):
        c = Counter()
        for m, a in p.items():
            for n, b in q.items():
                c[tuple(u + v for u, v in zip(m, n))] += a * b
        return {m: value for m, value in c.items() if value}

    def parse(self, rows, max_degree):
        assert isinstance(rows, list)
        out = {}
        for item in rows:
            assert set(item) == {'coefficient', 'monomial'}
            assert type(item['coefficient']) is int and item['coefficient'] != 0
            names = item['monomial']
            assert type(names) is list and all(type(n) is str for n in names)
            assert names == sorted(names) and len(names) <= max_degree
            exp = list(self.zero)
            for name in names:
                exp[self.index[name]] += 1
            exp = tuple(exp)
            assert exp not in out, ('duplicate monomial', names)
            out[exp] = item['coefficient']
        return out

    def evaluate(self, p, values):
        assert set(values) == set(self.names)
        terms = []
        for m, c in p.items():
            for name, exponent in zip(self.names, m):
                if exponent:
                    c *= values[name] ** exponent
            terms.append(c)
        return sum(terms)


def formula_value(node, signs):
    op, *args = node
    if op == 'sign':
        name, sense = args
        return signs[name] == {'negative': -1, 'zero': 0, 'positive': 1}[sense]
    values = [formula_value(n, signs) for n in args]
    if op == 'not':
        assert len(values) == 1
        return not values[0]
    assert len(values) == 2
    assert op in ('and', 'or')
    return all(values) if op == 'and' else any(values)


def gate_values(data, values):
    for name, op, args in data['logic_gates']:
        assert name not in values
        assert all(a in values for a in args)
        u = values[args[0]]
        if op == 'not':
            assert len(args) == 1
            values[name] = int(not u)
        else:
            assert len(args) == 2 and op in ('and', 'or')
            v = values[args[1]]
            values[name] = int(bool(u) and bool(v)) if op == 'and' else int(bool(u) or bool(v))
    return values


def check_file(path):
    payload = path.read_bytes()
    assert sha256(payload).hexdigest() == EXPORT_PINS[path.name]
    data = json.loads(payload, object_pairs_hook=unique_object)
    names = data['inputs'] + data['witnesses']
    alg = Algebra(names)
    V, C, add, scale, mul = alg.variable, alg.constant, alg.add, alg.scale, alg.product
    atoms = {name: alg.parse(q, 2) for name, q in data['atoms'].items()}
    actual_residuals = [alg.parse(r, 2) for r in data['residuals']]
    expanded = alg.parse(data['expanded_polynomial'], 4)
    expected = []
    expected_witnesses = set()
    for name, q in atoms.items():
        em, e0, ep, z = [name + '_' + suffix for suffix in ('negative', 'zero', 'positive', 'magnitude')]
        expected_witnesses.update((em, e0, ep, z))
        for e in (em, e0, ep):
            expected.append(add(mul(V(e), V(e)), scale(V(e), -1)))
        expected.append(add(V(em), V(e0), V(ep), C(-1)))
        expected.append(add(q, scale(mul(add(V(ep), scale(V(em), -1)), add(V(z), C(1))), -1)))
        expected.append(mul(V(e0), V(z)))
    for name, op, args in data['logic_gates']:
        expected_witnesses.add(name)
        u = V(args[0])
        if op == 'not':
            target = add(C(1), scale(u, -1))
        elif op == 'and':
            target = mul(u, V(args[1]))
        else:
            assert op == 'or'
            target = add(u, V(args[1]), scale(mul(u, V(args[1])), -1))
        expected.append(add(V(name), scale(target, -1)))
    output = data['logic_gates'][-1][0]
    expected.append(add(V(output), C(-1)))
    canon = lambda p: tuple(sorted(p.items()))
    assert Counter(map(canon, expected)) == Counter(map(canon, actual_residuals))
    assert expected_witnesses == set(data['witnesses'])
    independent_expansion = add(*(mul(r, r) for r in actual_residuals))
    assert independent_expansion == expanded
    degree = max(sum(m) for m in expanded)
    ledger = {
        'atoms': len(atoms), 'logic_gates': len(data['logic_gates']),
        'witnesses': len(data['witnesses']), 'residuals': len(actual_residuals),
        'degree': degree, 'monomials': len(expanded),
    }
    assert ledger == data['ledger']
    assert ledger['witnesses'] == 4 * ledger['atoms'] + ledger['logic_gates']
    assert ledger['residuals'] == 6 * ledger['atoms'] + ledger['logic_gates'] + 1

    if path.name == 'four_signal_quartic.json':
        d, y = V('d'), V('y')
        assert atoms == {'gap': d, 'limit_margin': add(scale(y, 2), scale(d, -1))}
        desired = lambda d, y: d > 0 and 2 * y >= d
    else:
        x, y = V('x'), V('y')
        assert atoms == {'x': x, 'C': add(x, scale(y, -2)), 'H': scale(add(mul(x, x), mul(x, y), scale(mul(y, y), -1)), 4)}
        desired = lambda x, y: x > 0 and x * x + x * y - y * y >= 0

    truth_cases = 0
    for signs_tuple in product((-1, 0, 1), repeat=len(atoms)):
        signs = dict(zip(atoms, signs_tuple))
        flags = {}
        for atom, s in signs.items():
            flags.update({atom + '_negative': int(s < 0), atom + '_zero': int(s == 0), atom + '_positive': int(s > 0)})
        values = gate_values(data, flags)
        assert values[output] == formula_value(data['formula'], signs)
        truth_cases += 1

    accepted = rejected = mutations = evaluations = 0
    for x, y in product(range(21), repeat=2):
        input_values = dict(zip(data['inputs'], (x, y)))
        # Atom values use only input coordinates; zeros pad as-yet undefined witnesses.
        padded = {name: input_values.get(name, 0) for name in names}
        values = dict(input_values)
        signs = {}
        for name, q in atoms.items():
            n = alg.evaluate(q, padded)
            signs[name] = (n > 0) - (n < 0)
            values.update({name + '_negative': int(n < 0), name + '_zero': int(n == 0), name + '_positive': int(n > 0), name + '_magnitude': max(abs(n) - 1, 0)})
        gate_values(data, values)
        claim = desired(x, y)
        assert formula_value(data['formula'], signs) == claim
        p = alg.evaluate(expanded, values)
        assert p == sum(alg.evaluate(r, values) ** 2 for r in actual_residuals)
        assert p == int(not claim)
        evaluations += 1
        accepted += claim
        rejected += not claim
        if claim:
            for witness in data['witnesses']:
                for change in (-1, 1, 3):
                    if values[witness] + change < 0:
                        continue
                    changed = dict(values)
                    changed[witness] += change
                    assert any(alg.evaluate(r, changed) != 0 for r in actual_residuals)
                    mutations += 1
    for seed in range(100):
        values = {name: ((seed + 1) * (i + 3) ** 2 + 7 * i) % 17 - 8 for i, name in enumerate(names)}
        assert alg.evaluate(expanded, values) == sum(alg.evaluate(r, values) ** 2 for r in actual_residuals)
        evaluations += 1
    return {
        'sha256': sha256(payload).hexdigest(), 'bytes': len(payload), 'ledger': ledger,
        'coefficient_identity': 'Exact dictionary equality: expanded polynomial = sum of squares of every emitted residual',
        'gadget_identity': 'Exact multiset equality to independently reconstructed sign and logic residuals',
        'complete_sign_truth_table_cases': truth_cases,
        'accepted_inputs': accepted, 'rejected_inputs': rejected,
        'single_witness_mutations_rejected': mutations,
        'expanded_SOS_integer_evaluations': evaluations,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-dir', type=Path, required=True)
    args = parser.parse_args()
    source = args.source_dir / 'emit_sign_certificate.py'
    assert sha256(source.read_bytes()).hexdigest() == PIN
    receipt = {
        'status': 'PASS', 'emitter_source_sha256': PIN,
        'scope': 'Author source read inertly and hashed only. Exported JSON parsed as data. Only this newly written independent algebra checker executed.',
        'files': {name: check_file(args.source_dir / 'exports' / name) for name in EXPORT_PINS},
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run this audit checker with assertions enabled; -O and -OO are forbidden')
    main()
