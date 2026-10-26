#!/usr/bin/env python3
"""Independent verification of finite acyclic-projection polynomial circuits.

No producer, optimizer, or search module is imported.  Each circuit block is
expanded only in its local source-variable/macro cuts.  Acyclic unit pivots
have unique integer-polynomial restorations; the undeleted equations after
these substitutions are equivalent to the source under projection.  The
last checked block is precisely their sum of squares.  This is the ordinary
integer zero-set-bijection argument; it makes no consistency assumption.

The raw pooling source and its unbounded arithmetic calibration are separate
dependencies, authenticated by verify_pooling.py and the accompanying proof.
"""
import argparse
import copy
import hashlib
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PRIME = 1000000007
WEIGHTS = {
    'all5': [([0, 1, 2, 3, 4], 'base')],
    'staged': [([0, 1, 2], 'base'), ([3, 4], 'one')],
    'paired': [([0], 'direct'), ([1, 2], 'base'), ([3, 4], 'one')],
}
RAW_POOL_CACHE = set()


class VerificationError(ValueError):
    pass


def require(test, message):
    if not test:
        raise VerificationError(message)


def polynomial(raw, n):
    """Parse literal collected coefficients without permitting aliases."""
    require(type(raw) is list, 'Terms must be a list')
    answer = {}
    for term in raw:
        require(type(term) is list and len(term) == 2, 'Malformed term')
        coefficient, monomial = term
        require(type(coefficient) is int and coefficient != 0,
                'A coefficient must be a nonzero integer')
        require(type(monomial) is list and all(type(j) is int and 0 <= j < n for j in monomial),
                'Invalid source variable index')
        require(monomial == sorted(monomial), 'Source monomial is not sorted')
        key = tuple(monomial)
        require(key not in answer, 'Duplicate source monomial')
        answer[key] = coefficient
    return answer


def addition(a, b, sign=1):
    answer = dict(a)
    for m, c in b.items():
        value = answer.get(m, 0) + sign * c
        if value:
            answer[m] = value
        else:
            answer.pop(m, None)
    return answer


def multiplication(a, b):
    answer = defaultdict(int)
    for m, c in a.items():
        for t, d in b.items():
            answer[tuple(sorted(m + t))] += c * d
    return {m: c for m, c in answer.items() if c}


def local_expression(nodes, start, end, cuts):
    """Expand one block only; discard a temporary after its last local use."""
    require(type(start) is int and type(end) is int and 0 <= start <= end < len(nodes),
            'Invalid block interval')
    use = Counter()
    for index in range(start, end + 1):
        node = nodes[index]
        if node[0] in ('+', '-', '*'):
            for ref in node[1:]:
                require(type(ref) is int and 0 <= ref < index, 'Circuit is not acyclic')
                require(ref >= start or ref in cuts, 'Unlisted external block register')
                if ref >= start:
                    use[ref] += 1
    values = {}
    for index in range(start, end + 1):
        node = nodes[index]
        if node[0] == 'const':
            value = {(): node[1]} if node[1] else {}
        else:
            require(node[0] in ('+', '-', '*'), 'Input variable inside arithmetic block')
            def argument(ref):
                return values[ref] if ref >= start else {(cuts[ref],): 1}
            left, right = argument(node[1]), argument(node[2])
            if node[0] == '*':
                value = multiplication(left, right)
            else:
                value = addition(left, right, 1 if node[0] == '+' else -1)
            for ref in node[1:]:
                if ref >= start:
                    use[ref] -= 1
                    if use[ref] == 0:
                        del values[ref]
        values[index] = value
    return values[end]


def weighted_data(poly, degree, norm, leading):
    max_degree = max((sum(degree[j] for j in monomial) for monomial in poly), default=0)
    coefficient_norm_bound = 0
    top = 0
    for monomial, coefficient in poly.items():
        coefficient_norm_bound += abs(coefficient) * math.prod(norm[j] for j in monomial)
        if sum(degree[j] for j in monomial) == max_degree:
            value = coefficient % PRIME
            for j in monomial:
                value = value * leading[j] % PRIME
            top = (top + value) % PRIME
    return max_degree, coefficient_norm_bound, top


def profile_definitions(source, selection):
    n = len(source['variables'])
    rows = [polynomial(row['terms'], n) for row in source['residuals']]
    require(type(selection['steps']) is list, 'Pivot list is missing')
    definitions = {}
    removed = set()
    for step in selection['steps']:
        r, v = step['row'], step['variable']
        require(type(r) is int and 0 <= r < len(rows), 'Invalid pivot row')
        require(type(v) is int and 0 <= v < n, 'Invalid pivot variable')
        require(r not in removed and v not in definitions, 'A pivot row or variable was reused')
        epsilon = rows[r].get((v,))
        require(epsilon in (-1, 1), 'Pivot slope is not a unit')
        require(all(v not in m for m in rows[r] if m != (v,)), 'Pivot variable occurs nonlinearly')
        definitions[v] = (r, {m: -epsilon * c for m, c in rows[r].items() if m != (v,)})
        removed.add(r)
    retained = [v for v in range(n) if v not in definitions]
    order, seen, visiting = [], set(retained), set()
    def visit(v):
        if v in seen:
            return
        require(v not in visiting, 'Cyclic pivot definitions')
        visiting.add(v)
        for monomial in definitions[v][1]:
            for j in monomial:
                visit(j)
        visiting.remove(v)
        seen.add(v)
        order.append(v)
    for v in definitions:
        visit(v)
    require(len(seen) == n, 'Not every source coordinate is restorable')
    return rows, definitions, removed, retained, order


def expected_pool(block, macro_ids):
    groups = block['groups']
    z = block['quotient_index']
    if block['weights'] == 'direct':
        require(len(groups) == 1, 'Direct block must contain one group')
        j = groups[0]
        return {(macro_ids[(j, 'delta')],): 1,
                tuple(sorted((z, macro_ids[(j, 'T')]))): 1}
    result = {tuple(sorted([z] + [macro_ids[(j, 'T')] for j in groups])): -1}
    for j in groups:
        variables = ([macro_ids[(j, 'base')]] if block['weights'] == 'base' else [])
        variables += [macro_ids[(j, 'E')]]
        variables += [macro_ids[(k, 'T')] for k in groups if k != j]
        monomial = tuple(sorted(variables))
        result[monomial] = result.get(monomial, 0) + 1
    return {m: c for m, c in result.items() if c}


def verify_factored_source_rows(rows, n, pool, source_hash):
    """Bind every factored pool to the actual expanded frozen source row."""
    pool_hash = hashlib.sha256(json.dumps(pool, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    cache_key = (source_hash, pool_hash)
    if cache_key in RAW_POOL_CACHE:
        return
    groups = [{field: polynomial(g[field], n) for field in ('base', 'T', 'E', 'delta') if field in g}
              for g in pool['groups']]
    def product(factors):
        answer = {(): 1}
        for factor in factors:
            answer = multiplication(answer, factor)
        return answer
    offset = len(rows) - len(pool['blocks'])
    for i, block in enumerate(pool['blocks']):
        indices = block['groups']
        z = {(block['quotient_index'],): 1}
        if block['weights'] == 'direct':
            j = indices[0]
            expected = addition(groups[j]['delta'], multiplication(z, groups[j]['T']))
        else:
            expected = {m: -c for m, c in product([z] + [groups[j]['T'] for j in indices]).items()}
            for j in indices:
                factors = ([groups[j]['base']] if block['weights'] == 'base' else [])
                factors += [groups[j]['E']]
                factors += [groups[k]['T'] for k in indices if k != j]
                expected = addition(expected, product(factors))
        require(expected == rows[offset + i], 'Factored macros do not equal the frozen pool source row')
    RAW_POOL_CACHE.add(cache_key)


def dependence_witness(nodes, output, nvars, label):
    """Nonzero formal derivatives at exact modular points prove occurrence."""
    remaining = set(range(nvars))
    witnesses = []
    for attempt in range(1, 9):
        point = [int.from_bytes(hashlib.sha256(
            ('projection-occurrence:' + label + ':' + str(attempt) + ':' + str(i)).encode()).digest(), 'big') % PRIME
                 for i in range(nvars)]
        values = []
        for node in nodes:
            op = node[0]
            if op == 'var':
                value = point[node[1]]
            elif op == 'const':
                value = node[1] % PRIME
            elif op == '+':
                value = (values[node[1]] + values[node[2]]) % PRIME
            elif op == '-':
                value = (values[node[1]] - values[node[2]]) % PRIME
            else:
                value = values[node[1]] * values[node[2]] % PRIME
            values.append(value)
        adjoint = [0] * len(nodes)
        adjoint[output] = 1
        for i in range(output, -1, -1):
            node, weight = nodes[i], adjoint[i]
            if not weight or node[0] in ('var', 'const'):
                continue
            op, a, b = node
            if op == '+':
                adjoint[a] = (adjoint[a] + weight) % PRIME
                adjoint[b] = (adjoint[b] + weight) % PRIME
            elif op == '-':
                adjoint[a] = (adjoint[a] + weight) % PRIME
                adjoint[b] = (adjoint[b] - weight) % PRIME
            else:
                adjoint[a] = (adjoint[a] + weight * values[b]) % PRIME
                adjoint[b] = (adjoint[b] + weight * values[a]) % PRIME
        hit = sorted(i for i in remaining if adjoint[i])
        if hit:
            witnesses.append({'attempt': attempt, 'point': point,
                              'nonzero_derivatives': [[i, adjoint[i]] for i in hit]})
            remaining.difference_update(hit)
        if not remaining:
            return {'modulus': PRIME, 'all_variables_proved_to_occur': True,
                    'witnesses': witnesses}
    raise VerificationError('No nonzero derivative witness found for variables ' + str(sorted(remaining)))


def verify(source_bytes, pool, selection, artifact, label, derivatives=True):
    source = json.loads(source_bytes)
    require(artifact.get('schema') == 'oriented-acyclic-polynomial-v1', 'Unknown circuit schema')
    require(artifact.get('domain') == 'unrestricted integers', 'Wrong polynomial domain')
    require(source.get('domain') == 'unrestricted integers', 'Wrong source domain')
    variant = selection['variant']
    require(variant in WEIGHTS and artifact.get('variant') == variant, 'Wrong source variant')
    require([(x['groups'], x['weights']) for x in pool['blocks']] == WEIGHTS[variant],
            'Pool selector does not match the authenticated variant')
    require(artifact['source_sha256'] == hashlib.sha256(source_bytes).hexdigest(), 'Source byte hash mismatch')
    rows, definitions, removed, inputs, order = profile_definitions(source, selection)
    n, nv = len(source['variables']), len(inputs)
    verify_factored_source_rows(rows, n, pool, artifact['source_sha256'])
    require(selection['variables'] == nv, 'Selected variable count is wrong')
    require(artifact['retained_source_indices'] == inputs, 'Retained source order is wrong')
    require(artifact['variables'] == [dict(source_index=i, **source['variables'][i]) for i in inputs],
            'Declared variable mapping is wrong')
    nodes = artifact['nodes']
    require(type(nodes) is list and len(nodes) >= nv, 'Missing nodes')
    for i, node in enumerate(nodes):
        require(type(node) is list and node, 'Malformed circuit node')
        op = node[0]
        if i < nv:
            require(node == ['var', i], 'Input nodes are not exactly the declared variables')
        elif op == 'const':
            require(len(node) == 2 and type(node[1]) is int, 'Noninteger literal constant')
        else:
            require(op in ('+', '-', '*') and len(node) == 3,
                    'Unsupported arithmetic operation')
            require(all(type(j) is int and 0 <= j < i for j in node[1:]), 'Non-acyclic node reference')
    roots = dict(zip(inputs, range(nv)))
    macro_registers, macro_ids = {}, {}
    defined = set()
    seen_residuals, residual_roots = [], []
    pool_start = len(rows) - len(pool['blocks'])
    require(pool_start >= 0, 'Too many pool blocks')
    position = nv
    completed_sos = False
    for block_index, block in enumerate(artifact['blocks']):
        require(not completed_sos, 'Data block follows final sum of squares')
        start, end = block['start'], block['root']
        require(start == position, 'Circuit blocks do not form an exact node partition')
        kind = block['kind']
        if kind == 'definition':
            v, r = block['variable'], block['source_row']
            require(v in definitions and v not in defined and definitions[v][0] == r,
                    'Unexpected or duplicate definition block')
            expected = definitions[v][1]
            cuts = {reg: j for j, reg in roots.items()}
            require(all(j in roots for mon in expected for j in mon), 'Definition precedes its dependencies')
            actual = local_expression(nodes, start, end, cuts)
            require(actual == expected, 'Definition block is not its unit-pivot restoration polynomial')
            roots[v] = end
            defined.add(v)
        elif kind == 'macro':
            require(len(defined) == len(definitions), 'Macro precedes complete source restoration')
            j, field, ident = block['group'], block['field'], block['formal_index']
            require(type(j) is int and 0 <= j < len(pool['groups']), 'Invalid macro group')
            require(field in ('base', 'T', 'E', 'delta') and field in pool['groups'][j], 'Invalid macro field')
            require((j, field) not in macro_ids and type(ident) is int and ident >= n and ident not in macro_registers,
                    'Repeated or invalid macro identifier')
            expected = polynomial(pool['groups'][j][field], n)
            actual = local_expression(nodes, start, end, {reg: k for k, reg in roots.items()})
            require(actual == expected, 'Macro block differs from its literal source expression')
            macro_ids[(j, field)] = ident
            macro_registers[ident] = end
        elif kind in ('residual', 'pool'):
            require(len(defined) == len(definitions), 'Residual precedes complete source restoration')
            r = block['source_row']
            require(type(r) is int and 0 <= r < len(rows) and r not in removed and r not in seen_residuals,
                    'Unexpected or duplicate retained residual')
            if kind == 'residual':
                require(r < pool_start, 'Pool row emitted without its declared factored block')
                expected = rows[r]
                cuts = {reg: j for j, reg in roots.items()}
            else:
                bi = block['pool_block']
                require(type(bi) is int and 0 <= bi < len(pool['blocks']) and r == pool_start + bi,
                        'Invalid factored pool selector')
                expected = expected_pool(pool['blocks'][bi], macro_ids)
                cuts = {reg: j for j, reg in roots.items()}
                cuts.update({reg: j for j, reg in macro_registers.items()})
            actual = local_expression(nodes, start, end, cuts)
            require(actual == expected, 'Retained residual or factored pool differs from its source')
            seen_residuals.append(r)
            residual_roots.append(end)
        elif kind == 'sum_of_squares':
            require(len(defined) == len(definitions), 'Final output omits source definitions')
            require(seen_residuals == [r for r in range(len(rows)) if r not in removed],
                    'Source-row partition is incomplete or out of order')
            require(artifact['residual_roots'] == residual_roots, 'Residual register list is wrong')
            formal = {reg: j for j, reg in enumerate(residual_roots)}
            expected = {(j, j): 1 for j in range(len(residual_roots))}
            require(local_expression(nodes, start, end, formal) == expected, 'Output is not exactly the sum of residual squares')
            require(end == artifact['output'] == len(nodes) - 1, 'Output is not the final certified register')
            completed_sos = True
        else:
            raise VerificationError('Unknown circuit block kind')
        position = end + 1
    require(completed_sos and position == len(nodes), 'Circuit block coverage is incomplete')
    expected_macros = {(j, f) for j, g in enumerate(pool['groups'])
                       for f in ('base', 'T', 'E', 'delta') if f in g}
    require(set(macro_ids) == expected_macros, 'Source macros are missing or extraneous')
    # Independently recompute weighted degree, l1 coefficient-norm bound,
    # and the homogeneous specialization through the acyclic definitions.
    degrees = {j: 1 for j in inputs}
    norms = {j: 1 for j in inputs}
    leading = {j: (j + 3) % PRIME for j in inputs}
    for j in order:
        degrees[j], norms[j], leading[j] = weighted_data(definitions[j][1], degrees, norms, leading)
    residual_data = [weighted_data(rows[r], degrees, norms, leading) for r in seen_residuals]
    maxd = max(d for d, bound, top in residual_data)
    degree = artifact['degree_certificate']
    require(degree['modulus'] == PRIME and degree['input_direction'] == 'source_index + 3',
            'Unsupported degree specialization')
    require(degree['source_degrees'] == [degrees[j] for j in range(n)], 'Source degree bounds are wrong')
    require(degree['retained_rows'] == seen_residuals, 'Degree rows do not match the output')
    require(degree['residual_degrees'] == [d for d, bound, top in residual_data], 'Residual degree bounds are wrong')
    wr = degree['witness_source_row']
    require(wr in seen_residuals, 'Leading-degree witness row is not retained')
    wd, wn, wt = residual_data[seen_residuals.index(wr)]
    require(wd == maxd and wt != 0 and degree['witness_top_residue'] == wt,
            'Leading-degree witness is zero, incorrect, or below the claimed degree')
    require(2 * maxd <= selection['degree_bound'], 'Projection exceeds its stated degree budget')
    # One residual has exact degree maxd. A sum of real polynomial squares
    # then has exact degree 2*maxd; its top squares cannot cancel.
    norm_square_sum = sum(bound * bound for d, bound, top in residual_data)
    live, pending = set(), [artifact['output']]
    while pending:
        j = pending.pop()
        if j in live:
            continue
        live.add(j)
        if nodes[j][0] in ('+', '-', '*'):
            pending.extend(nodes[j][1:])
    metrics = dict(variables=nv, residuals=len(seen_residuals), degree=2 * maxd,
                   eliminated_variables=len(definitions),
                   coefficient_height_strict_power_of_two=norm_square_sum.bit_length(),
                   binary_operations=sum(nodes[j][0] in ('+', '-', '*') for j in live),
                   maximum_literal_constant=max(abs(nodes[j][1]) for j in live if nodes[j][0] == 'const'),
                   stored_nodes=len(nodes))
    require(artifact['metrics'] == metrics, 'Computed polynomial metrics differ from declared metrics')
    result = {'name': label, 'status': 'PASS', **metrics,
              'unit_pivots_checked': len(definitions), 'circuit_blocks_checked': len(artifact['blocks']),
              'degree_witness_source_row': wr, 'degree_witness_nonzero_residue': wt,
              'coefficient_bound_kind': 'Every expanded coefficient has absolute value strictly below 2^reported_exponent'}
    if derivatives:
        result['variable_occurrence'] = dependence_witness(nodes, artifact['output'], nv, label)
    return result


def corruption_checks(raw, pool, profile, artifact, label):
    cases = []
    bad = copy.deepcopy(artifact)
    bad['domain'] = 'nonnegative integers'
    cases.append(('domain', pool, profile, bad))
    bad = copy.deepcopy(artifact)
    target = next(i for i, node in enumerate(bad['nodes']) if node[0] in ('+', '-', '*'))
    bad['nodes'][target][0] = '+' if bad['nodes'][target][0] != '+' else '-'
    cases.append(('changed_gate', pool, profile, bad))
    bad_profile = copy.deepcopy(profile)
    bad_profile['steps'][0]['variable'] = len(json.loads(raw)['variables'])
    cases.append(('changed_pivot', pool, bad_profile, artifact))
    bad = copy.deepcopy(artifact)
    bad['degree_certificate']['witness_top_residue'] = (bad['degree_certificate']['witness_top_residue'] + 1) % PRIME
    cases.append(('degree_witness', pool, profile, bad))
    bad_pool = copy.deepcopy(pool)
    bad_pool['blocks'][0]['groups'] = list(reversed(bad_pool['blocks'][0]['groups']))
    if bad_pool['blocks'][0]['groups'] == pool['blocks'][0]['groups']:
        bad_pool['blocks'][0]['groups'] = [4]
    cases.append(('pool_selector', bad_pool, profile, artifact))
    outcomes = []
    for name, p, s, a in cases:
        try:
            verify(raw, p, s, a, label, derivatives=False)
        except (VerificationError, KeyError, IndexError) as exc:
            outcomes.append({'mutation': name, 'status': 'REJECTED', 'reason': str(exc)})
        else:
            raise VerificationError('Corruption was accepted: ' + name)
    return outcomes


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--profile', help='Optional exact profile filename stem')
    parser.add_argument('--skip-corruptions', action='store_true')
    args = parser.parse_args()
    paths = sorted((ROOT / 'certificates').glob('*.json'))
    if args.profile:
        paths = [p for p in paths if p.stem == args.profile]
    require(bool(paths), 'No requested projection profiles found')
    results = []
    for path in paths:
        profile = json.loads(path.read_bytes())
        base = ROOT / 'sources' / profile['variant']
        raw = (base / 'equation.json').read_bytes()
        pool = json.loads((base / 'certificate.json').read_bytes())
        artifact = json.loads((ROOT / 'equations' / path.name).read_bytes())
        result = verify(raw, pool, profile, artifact, path.stem)
        require(path.stem == 'integer%d_degree%d' % (result['variables'], result['degree']), 'Profile filename disagrees with polynomial')
        if not args.skip_corruptions:
            result['corruption_controls'] = corruption_checks(raw, pool, profile, artifact, path.stem)
        results.append(result)
    receipt = {'status': 'PASS', 'checker': 'independent exact local-polynomial and weighted-degree audit',
               'scope': 'Finite algebra and explicit polynomial restorations; unbounded arithmetic calibration is a separate proof dependency',
               'profiles': results}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    # Keep the console compact; the optional receipt retains every derivative witness.
    brief = [{k: v for k, v in result.items() if k not in ('variable_occurrence', 'corruption_controls')}
             for result in results]
    print(json.dumps({'status': 'PASS', 'profiles': brief,
                      'nonzero_modular_derivative_witnesses': sum(r['variables'] for r in results),
                      'rejected_corruptions': sum(len(r.get('corruption_controls', [])) for r in results)},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
