"""Fold equal paired-port offsets into a shared selector-packing bias.

Only exact integer polynomial rewrites are used. The compiler retains the
parent source when none of the bounded candidate plans saves a gate.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import product
import json
from math import gcd
from pathlib import Path
import random

import group_projective_shared_history_rhs as shared
import group_projective_strong_unit_product as strong

execute = shared.execute
residuals = shared.residuals


def canon(coefficients):
    coefficients = tuple(coefficients)
    while len(coefficients) > 1 and coefficients[-1] == 0:
        coefficients = coefficients[:-1]
    return coefficients or (0,)


def add_poly(a, b, sign=1):
    return canon((a[i] if i < len(a) else 0) + sign*(b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b))))


def mul_poly(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return canon(out)


def div_poly(a, b):
    """Return an integral exact quotient, or None."""
    a, b = canon(a), canon(b)
    if b == (0,) or len(a) < len(b):
        return None
    rem = list(a)
    out = [0]*(len(a)-len(b)+1)
    for shift in range(len(out)-1, -1, -1):
        lead = rem[shift+len(b)-1]
        if lead % b[-1]:
            return None
        out[shift] = lead//b[-1]
        for i, value in enumerate(b):
            rem[shift+i] -= out[shift]*value
    return canon(out) if not any(rem) else None


def op(symbol, a, b):
    if isinstance(a, int) and isinstance(b, int):
        return a*b if symbol == '*' else a+b if symbol == '+' else a-b
    if symbol == '*':
        if a == 0 or b == 0: return 0
        if a == 1: return b
        if b == 1: return a
    if symbol == '+':
        if a == 0: return b
        if b == 0: return a
    if symbol == '-':
        if b == 0: return a
        if a == b: return 0
    if symbol in ('+', '*') and repr(a) > repr(b):
        a, b = b, a
    return (symbol, a, b)


def expression_nodes(expr):
    seen = set()
    def walk(e):
        if isinstance(e, tuple) and e not in seen:
            walk(e[1]); walk(e[2]); seen.add(e)
    walk(expr)
    return seen


def expression_poly(expr, ref_values):
    if isinstance(expr, int): return (expr,)
    if isinstance(expr, str): return ref_values[expr]
    symbol, a, b = expr
    a, b = expression_poly(a, ref_values), expression_poly(b, ref_values)
    return mul_poly(a, b) if symbol == '*' else add_poly(a, b, -1 if symbol == '-' else 1)


def existing_radix_polynomials(packet):
    P = 'controller__geometry_power' if packet['compute_length'] else 'P'
    values = {P: (0, 1)}
    available = {(0, 1): P}
    for name, symbol, a, b in packet['source']:
        if name == P:
            continue  # Treat the computed radix as one independent indeterminate.
        def value(v):
            return (v,) if isinstance(v, int) else values.get(v)
        aa, bb = value(a), value(b)
        if aa is None or bb is None:
            continue
        pp = mul_poly(aa, bb) if symbol == '*' else add_poly(aa, bb, -1 if symbol == '-' else 1)
        if len(pp) > 8:
            continue
        values[name] = pp
        if len(pp) > 1:
            available.setdefault(pp, name)
    return P, values, available


def bias_plan(packet, coefficients):
    """A finite candidate grammar; no global circuit-optimality claim."""
    P, values, available = existing_radix_polynomials(packet)
    def key(expr): return (len(expression_nodes(expr)), repr(expr))
    @lru_cache(None)
    def plan(poly):
        poly = canon(poly)
        if len(poly) == 1:
            return poly[0]
        if poly in available:
            return available[poly]
        candidates = []
        # Split at already paid powers P, P^2 or P^4.
        for split in (1, 2, 4):
            if split >= len(poly): continue
            power = (0,)*split+(1,)
            assert power in available
            low, high = canon(poly[:split]), canon(poly[split:])
            candidates.append(op('+', plan(low), op('*', available[power], plan(high))))
        # Factor by any already paid nonconstant radix polynomial.
        for divisor, name in available.items():
            if len(divisor) >= len(poly): continue
            quotient = div_poly(poly, divisor)
            if quotient is not None:
                candidates.append(op('*', name, plan(quotient)))
        common = 0
        for value in poly: common = gcd(common, abs(value))
        if common > 1:
            candidates.append(op('*', common, plan(tuple(v//common for v in poly))))
        assert candidates
        return min(candidates, key=key)
    target = canon(coefficients)
    choices = [plan(target)]
    # Paid repunits/factors can be useful additive baselines.
    for pp, name in available.items():
        if len(pp) <= len(target):
            choices.append(op('+', name, plan(add_poly(target, pp, -1))))
    best = min(choices, key=key)
    assert expression_poly(best, values) == target
    return best, values


def emit_expression(expr, source):
    registers = {}
    def emit(e):
        if not isinstance(e, tuple): return e
        if e not in registers:
            a, b = emit(e[1]), emit(e[2])
            name = f'port_bias_gate{len(registers)}'
            source.append((name, e[0], a, b))
            registers[e] = name
        return registers[e]
    result = emit(expr)
    assert len(registers) == len(expression_nodes(expr))
    return result


def rewrite(old):
    arities = [sum(edge[2] == i+1 for edge in old['edges']) for i in range(8)]
    eligible = [i for i in range(4) if arities[2*i] == arities[2*i+1] and arities[2*i] >= 2]
    candidates = []
    for bits in product((False, True), repeat=len(eligible)):
        pairs = [i for i, chosen in zip(eligible, bits) if chosen]
        coefficients = [1]*8
        for i in pairs:
            coefficients[2*i] = coefficients[2*i+1] = arities[2*i]
        expr, values = bias_plan(old, coefficients)
        added = len(expression_nodes(expr))
        saving = 2*len(pairs)-added
        candidates.append((saving, -added, tuple(pairs), expr, coefficients, values))
    best = max(candidates, key=lambda row: row[:3])
    saving, _, pairs, expr, coefficients, values = best
    assert saving >= 0
    if saving == 0:
        pairs = ()
        expr, values = bias_plan(old, [1]*8)
        coefficients = [1]*8
        assert len(expression_nodes(expr)) == 0
    rows = {row[0]: row for row in old['source']}
    P = 'controller__geometry_power' if old['compute_length'] else 'P'
    ports = []
    for port in range(1, 9):
        terms = [f'controller__edge_hat{e}' for e, edge in enumerate(old['edges']) if edge[2] == port]
        value = terms[0] if terms else 1
        for index, term in enumerate(terms[1:], 1):
            name = f'controller__port{port}_sum{index}'
            assert rows[name] == (name, '+', value, term)
            value = name
        if len(terms) > 1:
            name = f'controller__port{port}'
            assert rows[name] == (name, '-', value, len(terms)-1)
            value = name
        ports.append(value)
    value = ports[-1]
    for index in range(6, -1, -1):
        mult, total = f'selection__Spack_mult{index}', f'selection__Spack_sum{index}'
        assert rows[mult] == (mult, '*', P, value)
        assert rows[total] == (total, '+', ports[index], mult)
        value = total
    for i in range(4):
        name = f'history__dS{i}'
        assert rows[name] == (name, '-', ports[2*i], ports[2*i+1])
    redirects = {}
    consumers = {}
    for i in pairs:
        for port in (2*i+1, 2*i+2):
            name = f'controller__port{port}'
            raw = f'controller__port{port}_sum{arities[port-1]-1}'
            assert rows[name] == (name, '-', raw, arities[port-1]-1)
            users = {n for n, _, a, b in old['source'] if name in (a, b)}
            assert len(users) == 2 and f'history__dS{i}' in users
            assert all(n == f'history__dS{i}' or n.startswith('selection__Spack_') for n in users)
            assert not any(name in pair for pair in old['comparisons'])
            redirects[name] = raw
            consumers[name] = sorted(users)
    batch = rows['selection__Sbatch']
    assert batch[:3] == ('selection__Sbatch', '-', 'selection__Spack_sum0')
    assert values[batch[3]] == (1,)*8
    changed = set(redirects)
    boundaries = {'selection__Sbatch', *(f'history__dS{i}' for i in pairs)}
    for name, _, a, b in old['source']:
        if (a in changed or b in changed) and name not in boundaries:
            changed.add(name)
    assert all(name in redirects or name.startswith('selection__Spack_') for name in changed)
    leaves = set()
    def gather(e):
        if isinstance(e, str): leaves.add(e)
        elif isinstance(e, tuple): gather(e[1]); gather(e[2])
    gather(expr)
    assert not (leaves & changed), 'bias must not reuse a changed port or packing register'
    bias_source = []
    bias = emit_expression(expr, bias_source)
    source = []
    for name, symbol, a, b in old['source']:
        if name in redirects: continue
        if name == 'selection__Sbatch': b = bias
        source.append((name, symbol, redirects.get(a, a), redirects.get(b, b)))
    source += bias_source
    source = shared.factored.index.parent.sort_source(source, {'x', *old['auxiliaries']})
    counts = Counter('M' if symbol == '*' else 'A' for _, symbol, _, _ in source)
    assert len(source) == old['operations']-saving
    return dict(old, source=source, operations=len(source), multiplications=counts['M'],
        additions_subtractions=counts['A'], paired_port_bias_folding=True,
        port_arities=arities, folded_port_pairs=list(pairs), removed_port_offsets=redirects,
        audited_private_port_consumers=consumers, selector_bias_coefficients=coefficients,
        selector_bias_source=bias_source, selector_bias_register=bias,
        port_bias_saving=dict(operations=saving, multiplications=old['multiplications']-counts['M'],
                              additions_subtractions=old['additions_subtractions']-counts['A']),
        candidate_plan_costs=[dict(pairs=list(row[2]), added_operations=-row[1], saving=row[0])
                              for row in candidates])


def build(codes, alpha=24, beta=12, variant='strong', controller_mask=False, compute_length=False):
    if variant == 'strong':
        old = strong.build(codes, alpha, beta, controller_mask, compute_length)
    else:
        old = shared.build(codes, alpha, beta, variant, controller_mask, compute_length)
    return rewrite(old)


def polynomial_source(packet):
    return (strong if packet.get('strong_unit_merged') else shared).polynomial_source(packet)


def degree_top(packet, weights):
    return (strong if packet.get('strong_unit_merged') else shared).degree_top(packet, weights)


def verify():
    rng = random.Random(2783502)
    examples = [(), ((1, 2),), ((1, 1, 2),), ((1, 1, 2, 2),),
                ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
                (tuple(range(1, 9))*2,), (tuple(range(1, 9))*3,)]
    records, cases, example = [], 0, None
    for codes in examples:
      for variant in ('four', 'six', 'shifted', 'strong'):
       for reuse in (False, True):
        probe = shared.build(codes)
        if reuse and probe['m'] < 8: continue
        for comp in (False, True):
            old = (strong.build(codes, controller_mask=reuse, compute_length=comp) if variant == 'strong'
                   else shared.build(codes, variant=variant, controller_mask=reuse, compute_length=comp))
            packet = rewrite(old)
            source, out = polynomial_source(packet)
            prior, prior_out = polynomial_source(old)
            assert packet['auxiliaries'] == old['auxiliaries']
            assert packet['comparisons'] == old['comparisons']
            saved = packet['port_bias_saving']['operations']
            assert len(source) == len(prior)-saved
            for case in range(24):
                z = {name: rng.randrange(1, 7) if case < 16 else rng.randrange(-4, 5)
                     for name in packet['parameters']+packet['auxiliaries']}
                env, before = execute(source, z), execute(prior, z)
                P = env['controller__geometry_power'] if comp else z['P']
                bias = packet['selector_bias_register']
                assert env[bias] == sum(c*P**i for i, c in enumerate(packet['selector_bias_coefficients']))
                assert env['selection__Sbatch'] == before['selection__Sbatch']
                assert all(env[name] == before[name] for name, _, _, _ in source
                           if name in before and not name.startswith('selection__Spack_'))
                assert residuals(packet, env) == residuals(old, before)
                assert env[out] == before[prior_out]
                cases += 1
            weights = {name: 1+i % 3 for i, name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap'] = 1
            degree = degree_top(packet, weights)[0]
            counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
            records.append(dict(m=packet['m'], port_arities=packet['port_arities'], variant=variant,
                controller_mask=reuse, compute_length=comp, certificate_operations=packet['operations'],
                polynomial_operations=len(source), polynomial_M=counts['M'], polynomial_A=counts['A'],
                equations=packet['equations'], positive_witnesses=packet['positive_witnesses'],
                exact_degree=degree, saving=packet['port_bias_saving'],
                folded_port_pairs=packet['folded_port_pairs'], selector_bias_source=packet['selector_bias_source']))
            if codes == examples[4] and variant == 'strong' and reuse and comp:
                example = dict(packet, polynomial_finalizer=source[packet['operations']:], polynomial_output=out)
                assert (saved, len(source), degree) == (1, 278, 3502)
            if codes in (examples[5], examples[6]):
                assert saved == 7
    return dict(status='PASS_GROUP_PROJECTIVE_PORT_BIAS_FOLDING', records=records,
        source_example=example, complete_residual_and_polynomial_identity_cases=cases,
        signed_assignments=cases//3,
        scope='Exact polynomial identity on unchanged supplied coordinates. Savings depend on audited equal port arities and paid bias circuit; no universal numerical alphabet or global circuit optimum is asserted.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
