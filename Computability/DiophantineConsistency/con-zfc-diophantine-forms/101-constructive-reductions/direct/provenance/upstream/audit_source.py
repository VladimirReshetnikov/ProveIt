#!/usr/bin/env python3
"""Independent local-source audit of the materialized direct compiler.

This checks polynomial transformation and finite local controls. It does not
assert a ZFC refutation, prove consistency, or replace the universal proofs.
"""
import argparse
import importlib.util
import json
import sys
from hashlib import sha256
from pathlib import Path
from random import Random


def require(test, message):
    if not test:
        raise RuntimeError(message)


def sparse(rows):
    out = {}
    for r in rows:
        m = tuple(sorted(r['monomial']))
        out[m] = out.get(m, 0) + r['coefficient']
    return {m: c for m, c in out.items() if c}


def eval_rows(rows, env, modulus=None):
    total = 0
    for row in rows:
        term = row['coefficient']
        for name in row['monomial']:
            term *= env[name]
            if modulus:
                term %= modulus
        total += term
        if modulus:
            total %= modulus
    return total


def branch_env(branch, env, modulus=None):
    out = dict(env)
    for definition in branch['wires']:
        out[definition['name']] = eval_rows(definition['value'], out, modulus)
    return out


def reduced_value(original, env, index, modulus):
    total = 1
    for branch in original['horn_source']['branches']:
        local = branch_env(branch, env, modulus)
        value = sum(eval_rows(r, local, modulus) ** 2
                    for r in branch['quadratic_residuals'][len(branch['wires']):])
        total = total * value % modulus
    M = env['M0'] + 1
    accumulator = env['Sp'] * (1 + env['v'] * M) - env['S'] * (1 + env['p'] * M) * (1 + env['q'] * M)
    D = 1 + (index + 1) * env['y']
    rows = [accumulator,
            env['x'] - env['S'] - D * env['u'],
            D - env['S'] - env['r'] - 1,
            env['x'] - env['Sp'] - (D + env['y']) * env['vq'],
            D + env['y'] - env['Sp'] - env['rp'] - 1]
    return (total + sum(r * r for r in rows)) % modulus


def circuit_value(builder, pair, inputs, modulus):
    values = dict(inputs)
    for row in builder.rows:
        out = row['gate']
        require(out is not None, 'unexpected nongate in source circuit')
        residual = 0
        out_coefficient = 0
        for coefficient, monomial in row['terms']:
            if out in monomial:
                require(monomial == [out], 'nonlinear output definition')
                out_coefficient += coefficient
                continue
            term = coefficient
            for variable in monomial:
                require(variable in values, 'nontopological circuit')
                term = term * values[variable] % modulus
            residual += term
        require(out_coefficient == 1, 'nonunit output coefficient')
        values[out] = -residual % modulus
    def atom(a):
        return a[1] if a[0] == 'c' else values[a[1]]
    return (atom(pair[0]) - atom(pair[1])) % modulus


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path, default=here/'affine_shared_step.json')
    parser.add_argument('--source', type=Path, default=here/'wire_eliminated_source.json')
    default_builder = here/'build_equation.py'
    if not default_builder.exists():
        default_builder = here.parent/'output/con_zfc_shared_certificates/direct/build_equation.py'
    parser.add_argument('--builder', type=Path, default=default_builder)
    parser.add_argument('--output', type=Path, default=here/'SOURCE_AUDIT.json')
    args = parser.parse_args()
    original = json.loads(args.original.read_text())
    source = json.loads(args.source.read_text())
    require(len(source['horn_branches']) == 12, 'branch count')
    wire_rows = 0
    for old, new in zip(original['horn_source']['branches'], source['horn_branches']):
        require(old['name'] == new['name'], 'branch names')
        require(old['wires'] == new['definitions'], 'definition transcription')
        require(old['quadratic_residuals'][len(old['wires']):] == new['residuals'], 'residual transcription')
        known = set(['p', 'q', 'v', 'a', 'b', 'c', 'd'])
        for i, definition in enumerate(old['wires']):
            require(all(t['coefficient'] >= 0 and set(t['monomial']) <= known
                        for t in definition['value']), 'nonnegative triangular definition')
            expected = sparse([{'coefficient': 1, 'monomial': [definition['name']]}] +
                              [{'coefficient': -t['coefficient'], 'monomial': t['monomial']}
                               for t in definition['value']])
            require(sparse(old['quadratic_residuals'][i]) == expected, 'wire equation identity')
            known.add(definition['name'])
            wire_rows += 1
    require(wire_rows == 56, 'wire occurrence count')

    spec = importlib.util.spec_from_file_location('candidate_builder', args.builder)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(args.builder.resolve().parent))
    spec.loader.exec_module(module)
    b = module.Builder()
    names = ['x', 'y', 'm', 'M0', 'p', 'q', 'v', 'a', 'b', 'c', 'd', 'S', 'Sp', 'u', 'r', 'vq', 'rp']
    env_nodes = {name: b.new(name) for name in names}
    index_node = b.new('i')
    pair = b.source_pair(source, env_nodes, index_node, False)
    rng = Random(20261024)
    cases = 0
    for _ in range(300):
        env = {name: rng.randrange(10) for name in names}
        i = rng.randrange(5)
        inputs = {node[1]: env[name] for name, node in env_nodes.items()}
        inputs[index_node[1]] = i
        for modulus in [1000003, 1000033, 1000037]:
            lhs = circuit_value(b, pair, inputs, modulus)
            rhs = reduced_value(original, env, i, modulus)
            require(lhs == rhs, 'source circuit differs from literal source')
            cases += 1

    fixtures = []
    for branch in original['horn_source']['branches']:
        env = dict(a=0, b=1, c=2, d=1, p=0, q=0, v=0)
        if branch['name'] == 'mp':
            env.update(p=1, v=2, q=32)
        elif branch['name'] == 'gen':
            env.update(a=1, p=2)
        local = branch_env(branch, env)
        if branch['name'] not in ['truth', 'mp']:
            env['v'] = -eval_rows(branch['quadratic_residuals'][-1], local)
            local['v'] = env['v']
        require(all(eval_rows(row, local) == 0 for row in branch['quadratic_residuals']),
                'exact selected-branch fixture fails')
        env['m'] = max(env['p'], env['q'], env['v'])
        env['M0'] = 1
        env['S'] = 1 + 2 * env['v']
        env['Sp'] = (1 + 2 * env['p']) * (1 + 2 * env['q'])
        env['y'] = max(env['S'], env['Sp']) + 1
        D, DD = env['y'] + 1, 2 * env['y'] + 1
        env['x'] = env['S'] + D * ((env['Sp'] - env['S']) * pow(D, -1, DD) % DD)
        env['u'], env['r'] = env['x'] // D, D - env['S'] - 1
        env['vq'], env['rp'] = env['x'] // DD, DD - env['Sp'] - 1
        require(min(env.values()) >= 0, 'negative fixture coordinate')
        require(env['x'] == env['S'] + D * env['u'] and env['x'] == env['Sp'] + DD * env['vq'], 'beta quotient')
        require(env['Sp'] * (1 + 2 * env['v']) == env['S'] * (1 + 2 * env['p']) * (1 + 2 * env['q']), 'accumulator')
        inputs = {node[1]: env[name] for name, node in env_nodes.items()}
        inputs[index_node[1]] = 0
        for modulus in [1000003, 1000033, 1000037]:
            require(circuit_value(b, pair, inputs, modulus) == 0, 'selected-branch circuit fixture')
        # The modified accumulator residual is exactly its positive coefficient.
        changed = (env['Sp'] + 1) * (1 + 2 * env['v']) - env['S'] * (1 + 2 * env['p']) * (1 + 2 * env['q'])
        require(changed == 1 + 2 * env['v'] > 0, 'negative control')
        fixtures.append({'branch': branch['name'], 'largest_coordinate_bits': max(v.bit_length() for v in env.values())})

    result = dict(status='PASS', original_sha256=sha256(args.original.read_bytes()).hexdigest(),
                  source_sha256=sha256(args.source.read_bytes()).hexdigest(),
                  builder_sha256=sha256(args.builder.read_bytes()).hexdigest(),
                  triangular_wire_identities=wire_rows, branches=12,
                  finite_modular_source_comparisons=cases,
                  exact_selected_branch_fixtures=fixtures,
                  negative_accumulator_controls=12,
                  scope='Exact wire-definition identities plus finite source-circuit controls; not a proof of the infinite consistency equivalence.')
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
