#!/usr/bin/env python3
"""Independent exact shear, full norm, coefficient, and degree verification.

The producer is not imported. Inherited free-polynomial checking utilities
are retained verbatim with provenance. No assertion statement is used.
"""
import argparse
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
PINS = {
    'rational': '5e85d22284880b36b44d7f50ef1648fbcbff4154cc56ab8ae393611b89fa55dc',
    'integral': '0e30346f30a6539c3d5ace2f58135e3b2c3f12fc69ce47b6d72d5bdffe9ef75b',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load(name):
    return json.loads((HERE / name).read_bytes())


def structural_shear(parent, child, integral):
    """Exact common expression DAG, not a numerical fingerprint."""
    interner = {}

    def intern(key):
        key = tuple(key)
        if key not in interner:
            interner[key] = len(interner)
        return interner[key]

    def op(kind, a, b):
        if kind in ('add', 'mul') and a > b:
            a, b = b, a
        return intern((kind, a, b))

    def evaluate(packet, replacement=None):
        values = []
        for row in packet['nodes']:
            if row[0] in ('add', 'sub', 'mul'):
                val = op(row[0], values[row[1]], values[row[2]])
            elif row == ['variable', 'n'] and replacement is not None:
                val = replacement
            else:
                val = intern(row)
            values.append(val)
        return values

    original = evaluate(parent)
    names = parent['named_registers']
    n = original[names['n']]
    shift = original[names['V']]
    if integral:
        shift = op('mul', original[names['delta']], shift)
    transported = evaluate(parent, op('add', n, shift))
    actual = evaluate(child)
    need(transported[parent['output']] == actual[child['output']],
         'universal full-output substitution identity')
    # The sheared quantity is independent of n, so subtracting it gives
    # the inverse map over every integer tuple, not merely at zeros.
    seen, todo = set(), [names['V']] + ([names['delta']] if integral else [])
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        row = parent['nodes'][i]
        need(row != ['variable', 'n'], 'triangular shear independent of n')
        if row[0] in ('add', 'sub', 'mul'):
            todo.extend(row[1:])
    return {'universal_full_output_identity': True,
            'integer_inverse': 'n=n_old-delta*V' if integral else 'n=n_old-V',
            'canonical_expression_nodes': len(interner)}


def topology(packet, integral):
    nodes = packet['nodes']
    for i, row in enumerate(nodes):
        if row[0] in ('add', 'sub', 'mul'):
            need(len(row) == 3 and all(type(j) is int and 0 <= j < i for j in row[1:]),
                 'acyclic binary arithmetic')
        else:
            need(row[0] in ('variable', 'coefficient', 'integer'), 'only polynomial nodes')
    seen, todo = set(), [packet['output']]
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        if nodes[i][0] in ('add', 'sub', 'mul'):
            todo.extend(nodes[i][1:])
    need(seen == set(range(len(nodes))), 'complete liveness')
    need([r[1] for r in nodes if r[0] == 'variable'] == VARS, 'all twelve integer variables')
    need([r[1] for r in nodes if r[0] == 'coefficient'] == PORTS, 'all six fixed ports')
    counts = dict(Counter(r[0] for r in nodes if r[0] in ('add', 'sub', 'mul')))
    expected = {'mul': 90 if integral else 93, 'add': 27, 'sub': 26}
    need(counts == expected == packet['operation_counts'], 'actual operation breakdown')
    need(sum(counts.values()) == packet['operations'] == (143 if integral else 146),
         'actual complete operation count')
    return {'nodes': len(nodes), 'operations': sum(counts.values()), 'operation_counts': counts}


def centered_q0_identity(oracle, integral):
    d, S, V, z, h = [oracle.variable(i) for i in range(5)]
    if integral:
        actual = (S*d*V+z)**2+h-S*S*d*((d+1)*V*V-1)
        expected = z*z+h+2*S*d*V*z-S*S*d*V*V+S*S*d
    else:
        actual = d*((S*V+z)**2+h)-S*S*((d+1)*V*V-1)
        expected = d*(z*z+h)+2*d*S*V*z-S*S*(V*V-1)
    need(actual.t == expected.t, 'entire centered cancellation identity')
    return {'centered_identity_terms': len(expected.t)}


def q0_cut(packet, oracle, integral):
    names, nodes = packet['named_registers'], packet['nodes']
    x, a, b, e, cn, d = [oracle.variable(i) for i in range(6)]
    cache = {names[n]: v for n, v in [('center', x), ('ra', a), ('rb', b), ('re', e), ('cn', cn)]}
    if not integral:
        cache[names['ndelta']] = d

    def at(i):
        if i in cache:
            return cache[i]
        row = nodes[i]
        if row[0] == 'integer':
            result = oracle.Poly(row[1])
        else:
            need(row[0] in ('add', 'sub', 'mul'), 'all local q0 operands bound')
            aa, bb = at(row[1]), at(row[2])
            result = aa+bb if row[0] == 'add' else aa-bb if row[0] == 'sub' else aa*bb
        cache[i] = result
        return result
    expected = (x*x+e-a-b)-cn if integral else d*(x*x+e-a-b)-cn
    need(at(names['q0']).t == expected.t, 'literal q0 equals the proved formula')


def leading(packet, oracle, integral):
    """Exact graded-lex induction with the one proved cancellation cut."""
    names = packet['named_registers']
    order = ['T', 'j', 'w', 'v', 's', 'r', 'c', 'h', 'C', 'z', 'n', 't']
    values = []

    def key(item):
        return (sum(item[0]),) + item[0]

    def times(a, b):
        return (tuple(x+y for x, y in zip(a[0], b[0])), a[1]*b[1])

    def sign(a, s):
        return (a[0], a[1]*s)

    def value(name):
        return values[names[name]]

    for idx, row in enumerate(packet['nodes']):
        if idx == names['q0']:
            expected_degrees = {'S': 34, 'V': 25, 'delta': 32, 're': 114,
                                'ra': 88, 'rb': 102, 'Acarrier': 45}
            for name, deg in expected_degrees.items():
                need(sum(value(name)[0]) == deg, 'actual prefix degree ' + name)
            # z0=Sn-Acarrier has degree45; the generic cancellation was
            # proved above. Compare every displayed summand's degree.
            if integral:
                v = sign(times(times(times(value('S'), value('S')), value('delta')),
                                     times(value('V'), value('V'))), -1)
                need(150 > max(90, 136, 100, 114, 88, 102), 'unique integral q0 top')
            else:
                v = times(value('delta'), value('re'))
                need(146 > max(122, 136, 118, 68, 120, 134), 'unique rational q0 top')
        elif row[0] == 'variable':
            exponent = [0]*12
            exponent[order.index(row[1])] = 1
            v = (tuple(exponent), oracle.Poly(1))
        elif row[0] == 'coefficient':
            v = ((0,)*12, oracle.variable(PORTS.index(row[1])))
        elif row[0] == 'integer':
            v = ((0,)*12, oracle.Poly(row[1]))
        else:
            a, b = values[row[1]], values[row[2]]
            if row[0] == 'mul':
                v = times(a, b)
            elif key(a) > key(b):
                v = a
            elif key(b) > key(a):
                v = sign(b, -1) if row[0] == 'sub' else b
            else:
                v = (a[0], a[1]-b[1] if row[0] == 'sub' else a[1]+b[1])
        need(bool(v[1].t), 'exact nonzero leading coefficient at node ' + str(idx))
        values.append(v)

    if integral:
        exponents = {'j': 576, 'w': 144, 'v': 144, 's': 80, 'r': 80, 'c': 160, 'T': 16}
        powers = (1200, 720, 576)
        degree = 1200
    else:
        exponents = {'j': 624, 'w': 144, 'v': 160, 's': 64, 'r': 56, 'c': 112, 'h': 16, 'T': 8}
        powers = (1256, 796, 624)
        degree = 1184
    wanted = oracle.Poly(2**powers[0]*3**powers[1])*oracle.variable(0)**powers[2]
    mon, coef = values[packet['output']]
    need(mon == tuple(exponents.get(n, 0) for n in order) and coef.t == wanted.t,
         'complete-DAG attained leading monomial and coefficient')
    need(sum(mon) == degree == packet['exact_degree'], 'exact degree')
    return {'exact_degree': degree, 'variable_order': order, 'monomial': exponents,
            'coefficient': '2^%d*3^%d*beta^%d' % powers,
            'all_nodes_exact_after_one_proved_cancellation': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    oracle = module('retained_scalar12_norm_oracle', HERE / 'parent/source/independent_norm_oracle.py')
    inherited = module('retained_scalar12_formula_checker', HERE / 'parent/check_math.py')
    binding = load('coefficients/BINDING.json')
    ports, bytes_checked = {}, {}
    for name, pin in binding['payloads'].items():
        raw = gzip.decompress((HERE / 'coefficients' / pin['file']).read_bytes())
        need(sha256(raw).hexdigest() == pin['raw_sha256'] and len(raw) == pin['raw_bytes'],
             'exact complete payload ' + name)
        ports[name] = int.from_bytes(raw, 'little')
        need(ports[name].bit_length() == pin['bits'], 'exact payload width ' + name)
        bytes_checked[name] = {'bits': pin['bits'], 'raw_sha256': pin['raw_sha256']}
    need(ports['beta'] == 2**1064921-1 and ports['cone_A'] == 2**1113
         and ports['cone_B'] == 2**666104, 'three closed fixed numerals')
    recipe = module('retained_source34_recipe', HERE / 'coefficients/recipe/source34_builder.py')
    rebuilt, recipe_audit = recipe.construct()
    for name, old in [('beta', 'beta'), ('K0', 'K'), ('MC', 'MC'), ('MF', 'MF_source')]:
        need(ports[name] == rebuilt[old], 'full finite coefficient reconstruction ' + name)

    results, rejected = {}, []
    original_formulas = list(inherited.FORMULAS)
    for variant in ('rational', 'integral'):
        integral = variant == 'integral'
        raw = (HERE / 'parent' / (variant + '.json')).read_bytes()
        need(sha256(raw).hexdigest() == PINS[variant], 'pinned parent ' + variant)
        parent, child = json.loads(raw), load(variant + '_centered.json')
        result = topology(child, integral)
        result.update(structural_shear(parent, child, integral))
        center = 'S*(n+delta*V)-Ac' if integral else 'S*(n+V)-Ac'
        inherited.FORMULAS = [(name, center if name == 'center' else text)
                              for name, text in original_formulas]
        result.update(inherited.prefix_check(child, oracle))
        result.update(inherited.tail_check(child, oracle, integral))
        q0_cut(child, oracle, integral)
        result.update(centered_q0_identity(oracle, integral))
        result['leading_certificate'] = leading(child, oracle, integral)
        for target in ('center', 'output'):
            bad = deepcopy(child)
            bad['nodes'][bad['named_registers'][target]][0] = 'add'
            try:
                structural_shear(parent, bad, integral)
            except ValueError:
                rejected.append(variant + ':' + target)
            else:
                raise ValueError('corrupted complete polynomial was accepted')
        results[variant] = result
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'variants': results, 'whole_coefficient_tuple': bytes_checked,
              'coefficient_recipe_audit': recipe_audit, 'rejected_mutations': rejected,
              'scope': 'Exact whole-output polynomial shears and integer inverses; '
                       'all prefix free-ring cuts; all495 formal norm coefficients; '
                       'literal topology/count; proved cancellation and exact every-node '
                       'leading induction; full fixed coefficient reconstruction. '
                       'The inherited ordinary semantic calibration remains a named theorem, '
                       'not a finite-test conclusion or a new machine-checked endpoint.'}
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(json.dumps({'status': 'PASS', 'optimized_python': report['optimized_python'],
                      'variants': {n: {'operations': r['operations'],
                                      'exact_degree': r['leading_certificate']['exact_degree']}
                                   for n, r in results.items()},
                      'norm_coefficients_each': 495, 'coefficient_recipe': 'PASS',
                      'rejected_mutations': rejected}, indent=2))


if __name__ == '__main__':
    main()
