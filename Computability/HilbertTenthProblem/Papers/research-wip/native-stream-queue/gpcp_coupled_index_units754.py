"""Couple all three linear targets to K in the complete positive GPCP source.

A positive projection to the selected fixed-target757 parent changes only
F0 and bound_beta in each AND core.  It has exactly four preimages over each
positive parent zero and an identity section.  All arithmetic is paid.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path
import random

import gpcp_index_linear_units757 as parent

PARENT_SHA256 = 'a8b213386863857dae8c98f06a2ab41b297e05e6742b91217f538efaf7087774'
PREFIXES = parent.PREFIXES
AND_PREFIXES = ('and__', 'hist__and__')
PRIMES = parent.PRIMES
exact_equal = parent.exact_equal


def flags(inline_initial, and_bounds, geometry_bounds):
    assert all(type(v) is bool for v in (inline_initial, and_bounds, geometry_bounds))
    return inline_initial, and_bounds, geometry_bounds


def parent_hash_guard():
    assert hashlib.sha256(Path(parent.__file__).read_bytes()).hexdigest() == PARENT_SHA256


@lru_cache(None)
def _canonical_parent(inline, ands, geo):
    return parent.build(parent_stage=763, inline_initial=inline, and_bounds=ands,
                        geometry_bounds=geo, index_units=True, linear_units=True)


def canonical_parent(inline_initial=True, and_bounds=True, geometry_bounds=True):
    key = flags(inline_initial, and_bounds, geometry_bounds)
    parent_hash_guard()
    return deepcopy(_canonical_parent(*key))


def rewrite(old):
    assert type(old) is dict
    key = flags(*(old.get(k) for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    parent_hash_guard()
    assert exact_equal(old, _canonical_parent(*key)), 'complete exact-type canonical selected757 parent required'
    assert old['parent_stage'] == 763 and old['index_units'] is old['linear_units'] is True
    by = {n: (op, a, b) for n, op, a, b in old['source']}
    consumers = lambda x: {n for n, op, a, b in old['source'] if x in (a, b)}
    changes = {}; erased = set(); interfaces = []
    active = {k: old[k] for k in parent.degrees_parent.ACTIVE + ('history_packet',) if k != 'auxiliaries'}
    for pre in PREFIXES:
        r1, target, K = (pre+x for x in ('r1', 'tr1', 'R11'))
        r = 'J' if pre == 'geo__' else pre+'bs_packed'
        expected = {r1: ('+', r, 1), target: ('+', r1, r1),
                    K: ('-', pre+'R10b', pre+'hpm1'),
                    pre+'index_unit': ('-', K, r),
                    pre+'linear_unit': ('+', pre+'H17', target),
                    pre+'H17': ('-', pre+'aux_u_rhs', pre+'jc'),
                    pre+'H2': ('*', pre+'aux_u_rhs', pre+'aux_u_rhs')}
        assert all(by.get(n) == row for n, row in expected.items())
        assert consumers(r1) == {target} and consumers(target) == {pre+'linear_unit'}
        assert consumers(K) == {pre+'index_unit'}
        assert r1 not in parent.degrees_parent.leaves(active)
        changes[target] = ('+', K, K); erased.add(r1)
        interface = dict(prefix=pre, packed_index=r, coupled_index=K,
                         erased_private_successor=r1, target=target,
                         index_unit=pre+'index_unit', linear_unit=pre+'linear_unit')
        if pre in AND_PREFIXES:
            assert consumers(pre+'F0') == {pre+'shared_sum02', pre+'bs_packed'}
            assert consumers(pre+'bound_beta') == {pre+'bs_X_bound'}
            assert consumers(r) == {r1, pre+'bs_X_bound', pre+'index_unit'}
            assert {pre+'F0', pre+'bound_beta'} <= set(old['auxiliaries'])
            assert not {pre+'F0', pre+'bound_beta'} & parent.degrees_parent.leaves(active)
            assert by[pre+'bs_packed'] == ('+', pre+'F0', pre+'bs_p4')
            assert by[pre+'shared_sum02'] == ('+', pre+'F0', pre+'F2')
            assert by[pre+'bs_X_bound'] == ('+', r, pre+'bound_beta')
            assert by[pre+'bs_q'] == ('-', pre+'q', pre+'bs_Q')
            interface.update(project_F0=pre+'F0', project_beta=pre+'bound_beta',
                             checksum=pre+'bs_q', first_padding=pre+'first_padding_unit')
        interfaces.append(interface)
    for name, row in {'repunit_product': ('*', 'Bm1', 'J'),
                      'repunit_P': ('+', 'repunit_product', 1),
                      'Bm1': ('-', 'B', 1), 'B': ('*', 2**63, 'Q'),
                      'scale': ('*', 'input_bound', 'repunit_P'),
                      'and__q': ('*', 16, 'scale')}.items():
        assert by[name] == row
    rows = [(n, *changes.get(n, (op, a, b))) for n, op, a, b in old['source'] if n not in erased]
    assert not any(a in erased or b in erased for n, op, a, b in rows)
    rows = parent.degrees_parent.sorted_source(rows, old['parameters']+old['auxiliaries'])
    counts = Counter(op for n, op, a, b in rows)
    p = parent.compact_parent(old)
    p.update(source=rows, operations=len(rows), multiplications=counts['*'],
             additions_subtractions=counts['+']+counts['-'], equations=old['equations'],
             witnesses=old['witnesses'], parent_stage=757, parent_ancestor_stage=763,
             index_units=True, linear_units=True, coupled_linear_targets=True,
             coupled_interfaces=interfaces, coupled_erased_registers=sorted(erased),
             coupled_changed_definitions=changes,
             coupled_parent_source=list(old['source']),
             coupled_parent_comparisons=list(old['comparisons']),
             coupled_parent_unit_factors=list(old['unit_factors']),
             coupled_parent_unit_register=old['unit_register'],
             coupled_parent_sha256=PARENT_SHA256,
             identical_complete_integer_polynomial=False,
             positive_zero_surjection=True,
             positive_projection_fiber_cardinality=4,
             projection='For each AND: F0_parent=F0+index_unit-1; bound_beta_parent=bound_beta+1-index_unit. Every other supplied coordinate is retained.',
             positive_section='Identity on the full supplied positive zero set of the selected757 parent.',
             positive_projection_scope='Exactly four positive preimages over every positive parent zero, with an identity section, for every positive program parameter. This does not claim that every parameter/input admits a zero.')
    assert p['operations'] == old['operations']-3 and p['multiplications'] == old['multiplications']
    assert p['additions_subtractions'] == old['additions_subtractions']-3
    assert p['comparisons'] == old['comparisons'] and p['unit_factors'] == old['unit_factors']
    assert p['parameters'] == old['parameters'] and p['auxiliaries'] == old['auxiliaries']
    assert 'identical_positive_zero_set' not in p and 'positive_zero_bijection' not in p
    return p


@lru_cache(None)
def _build(inline, ands, geo):
    return rewrite(_canonical_parent(inline, ands, geo))


def build(*, inline_initial=True, and_bounds=True, geometry_bounds=True):
    key = flags(inline_initial, and_bounds, geometry_bounds)
    parent_hash_guard()
    return deepcopy(_build(*key))


def checked(packet):
    assert type(packet) is dict
    key = flags(*(packet.get(k) for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    parent_hash_guard()
    assert exact_equal(packet, _build(*key)), 'complete exact-type canonical754 packet required'


def polynomial_source(packet=None):
    if packet is None: packet = build()
    checked(packet)
    return parent.finalizer.polynomial_source(packet)


def checked_values(packet, values):
    checked(packet)
    assert type(values) is dict and set(values) == set(packet['parameters']+packet['auxiliaries'])
    assert all(type(n) is str and type(v) is int for n, v in values.items())


def evaluate(packet, values):
    checked_values(packet, values)
    rows, out = polynomial_source(packet)
    return parent.execute(rows, values)[out]


def project_assignment(packet, values):
    """Formal integer map; positivity is guaranteed only at positive zeros."""
    checked_values(packet, values)
    e = parent.execute(packet['source'], values); mapped = dict(values)
    for pre in AND_PREFIXES:
        epsilon = e[pre+'index_unit']
        mapped[pre+'F0'] += epsilon-1
        mapped[pre+'bound_beta'] += 1-epsilon
    return mapped


def lift_assignment(packet, values, *, recoder_delta=0, history_delta=0):
    """Four formal sections; on positive parent zeros all are positive zeros."""
    checked_values(packet, values)
    assert all(type(d) is int and d in (0, 2) for d in (recoder_delta, history_delta))
    lifted = dict(values)
    for pre, delta in zip(AND_PREFIXES, (recoder_delta, history_delta)):
        lifted[pre+'F0'] += delta
        lifted[pre+'bound_beta'] -= delta
    return lifted


def offzero_correction(packet, values):
    """Complete division-free correction after the explicit coordinate map."""
    checked_values(packet, values)
    old = canonical_parent(*(packet[k] for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    rows, out = polynomial_source(packet); before, target = parent.polynomial_source(old)
    e = parent.execute(rows, values)
    mapped = project_assignment(packet, values)
    past = parent.execute(before, mapped)
    expected = {f: e[f] for f in packet['unit_factors']}
    for pre in AND_PREFIXES:
        epsilon = e[pre+'index_unit']
        expected[pre+'index_unit'] = 1
        expected[pre+'bs_q'] = e[pre+'bs_q']-epsilon+1
        assert past[pre+'bs_packed'] == e[pre+'R11']-1
        assert past[pre+'R11'] == e[pre+'R11']
        assert past[pre+'linear_unit'] == e[pre+'linear_unit']
        assert past[pre+'bs_X_bound'] == e[pre+'bs_X_bound']
    expected['geo__linear_unit'] -= 2*(e['geo__index_unit']-1)
    assert all(past[f] == v for f, v in expected.items())
    assert all(past[pre+'P17'] == e[pre+'P17'] for pre in PREFIXES)
    at = lambda env, n: env[n] if isinstance(n, str) else n
    residuals = [at(e, a)-at(e, b) for a, b in packet['comparisons'][:-1]]
    old_residuals = [at(past, a)-at(past, b) for a, b in old['comparisons'][:-1]]
    assert residuals == old_residuals
    S = sum(v*v for v in residuals)
    W = prod(e[f] for f in packet['unit_factors']); oldW = prod(expected.values())
    excluded = {pre+'bs_q' for pre in AND_PREFIXES} | {pre+x for pre in PREFIXES for x in ('index_unit', 'linear_unit')}
    common = prod(e[f] for f in packet['unit_factors'] if f not in excluded)
    T = common*e['geo__index_unit']*prod(e[pre+'linear_unit'] for pre in AND_PREFIXES)
    correction = T*(prod(e[pre+'bs_q']-e[pre+'index_unit']+1 for pre in AND_PREFIXES)
                   *(e['geo__linear_unit']-2*(e['geo__index_unit']-1))
                   -prod(e[pre+'bs_q']*e[pre+'index_unit'] for pre in AND_PREFIXES)*e['geo__linear_unit'])
    assert oldW-W == correction
    assert e[out] == W*(1+S)-1 and past[target] == oldW*(1+S)-1
    assert past[target]-e[out] == correction*(1+S)
    return dict(new_output=e[out], projected_parent_output=past[target],
                new_product=W, projected_parent_product=oldW,
                retained_sos=S, correction=correction*(1+S))


def degree_dictionary(packet=None):
    if packet is None: packet = build()
    rows, _ = polynomial_source(packet)
    return parent.degrees_parent.raw_degrees(dict(packet, source=rows))


def leading_audit(packet, prime):
    assert type(prime) is int and prime in PRIMES
    rows, out = polynomial_source(packet); degree = degree_dictionary(packet)
    top = {n: i+2 for i, n in enumerate(packet['parameters']+packet['auxiliaries'])}
    for pre in PREFIXES: top[pre+'tau_gap'] = top[pre+'eta'] = top[pre+'zeta'] = 1
    assignment = dict(top)
    for n, op, a, b in rows:
        da = degree[a] if isinstance(a, str) else 0; db = degree[b] if isinstance(b, str) else 0
        va = top[a] if isinstance(a, str) else a; vb = top[b] if isinstance(b, str) else b
        top[n] = (va*vb if op == '*' else (va if da == degree[n] else 0)
                  +(1 if op == '+' else -1)*(vb if db == degree[n] else 0)) % prime
        for pre in PREFIXES:
            if n != pre+'R15': continue
            d = lambda x: degree[pre+x]
            high = d('cam2')+d('gam')
            assert degree[n] == high > max(2*d('wn2'), d('wn2')+d('cam2'), d('wn2')+d('gam'),
                                                2*d('gam'), d('a4m5')+2*d('R10a'))
            top[n] = 2*top[pre+'cam2']*top[pre+'gam'] % prime
    assert top[out] and all(top[f] for f in packet['unit_factors'])
    return dict(prime=prime, degree=degree[out], input_top_assignment=assignment,
                output_leader_value=top[out], factor_leader_values={f: top[f] for f in packet['unit_factors']})


def degree_audit(packet=None):
    if packet is None: packet = build()
    rows, out = polynomial_source(packet); d = degree_dictionary(packet)
    at = lambda n: d[n] if isinstance(n, str) else 0
    maximum = max(max(at(a), at(b)) for a, b in packet['comparisons'][:-1])
    assert d[out] == d[packet['unit_register']]+2*maximum
    return dict(exact_degree=d[out], propagated_upper_bound=d[out], unit_degree=d[packet['unit_register']],
                maximum_outer_degree=maximum, factor_degrees={f: d[f] for f in packet['unit_factors']},
                leading_certificates=[leading_audit(packet, prime) for prime in PRIMES],
                assurance='Guarded expanded main norms and nonzero evaluations of the complete top homogeneous output certify exact formal degree before program specialization.')


def ledger(packet=None):
    if packet is None: packet = build()
    rows, out = polynomial_source(packet); c = Counter(op for n, op, a, b in rows)
    return dict(certificate={k: packet[k] for k in ('operations', 'multiplications', 'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(rows), multiplications=c['*'], additions_subtractions=c['+']+c['-'], output=out),
                degree=degree_audit(packet))


def forms():
    yield from product((False, True), repeat=3)


def source_audit(cases=12):
    rng = random.Random(754757); count = Counter(); digest = hashlib.sha256()
    for key in forms():
        p = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        for case in range(cases):
            signed = case >= cases//2
            values = {n: rng.randrange(-2, 3) if signed else rng.randrange(1, 3)
                      for n in p['parameters']+p['auxiliaries']}
            if case % 4 == 0:
                values.update({f'hist__Shat{i}': 1 for i in range(57)})
                count['zero_selector_contexts'] += 1
            result = offzero_correction(p, values)
            digest.update(json.dumps({k: v % PRIMES[0] for k, v in result.items()}, sort_keys=True).encode())
            count['complete_projected_factor_and_output_corrections'] += 1
            count['signed_cases'] += signed
            if case < 2:
                old = canonical_parent(*key)
                past = parent.execute(old['source'], values)
                for dr, dh in product((0, 2), repeat=2):
                    lifted = lift_assignment(p, values, recoder_delta=dr, history_delta=dh)
                    e = parent.execute(p['source'], lifted)
                    expected = {f: past[f] for f in old['unit_factors']}
                    for pre, delta in zip(AND_PREFIXES, (dr, dh)):
                        expected[pre+'index_unit'] -= delta
                        expected[pre+'bs_q'] -= delta
                    for pre in PREFIXES:
                        expected[pre+'linear_unit'] += 2*(past[pre+'index_unit']-1)
                    assert all(e[f] == v for f, v in expected.items())
                    at = lambda env, n: env[n] if isinstance(n, str) else n
                    assert all(at(e, a)-at(e, b) == at(past, a)-at(past, b)
                               for a, b in p['comparisons'][:-1])
                    count['complete_formal_lift_factor_and_residual_maps'] += 1
    return dict(count, modular_result_digest=digest.hexdigest(),
                scope='Exact integer execution of both complete sources after the formal map; positivity is not imposed on the off-zero mapped tuple.')


def mathematical_audit():
    count = Counter(); survivors = Counter(); example = None
    for t in range(4, 10):
        q = 1 << t; Q = q//16
        for C, sigma in product((1, -1), repeat=2):
            lows = ((-C-(5-sigma)-2-8) % 16, 5-sigma, 2, 8)
            highsum = (q-C-sum(lows))//16
            for a in range(highsum+1):
                for b in range(highsum-a+1):
                    for c in range(highsum-a-b+1):
                        highs = (a, b, c, highsum-a-b-c)
                        F = tuple(16*h+l for h, l in zip(highs, lows))
                        assert sum(F) == q-C and all(0 < f < q for f in F)
                        r = sum(f*q**i for i, f in enumerate(F))
                        for epsilon in (1, -1):
                            rho = r+epsilon-1; population = rho.bit_count()
                            if sigma != 1 or C != epsilon: assert population > t
                            if epsilon == -1 and F[0] == 1: count['cross_radix_borrow_cases'] += 1
                            count['field_sign_cases'] += 1
                            if population != t: continue
                            mapped = (F[0]+epsilon-1,)+F[1:]
                            assert sigma == 1 and C == epsilon and all(0 < f < q for f in mapped)
                            assert sum(mapped) == q-1 and rho == sum(f*q**i for i, f in enumerate(mapped))
                            survivors[str((C, sigma, epsilon))] += 1
                            for beta in (1, 2, 17):
                                mapped_beta = beta+1-epsilon
                                assert mapped_beta > 0 and rho+mapped_beta == r+beta
                                count['positive_bound_projection_identities'] += 1
                            if q == 64 and F == (3, 20, 34, 8) and epsilon == -1:
                                example = dict(q=q, fields=list(F), packed_index=r, shifted_index=rho, population=population)
    assert example
    for logq, t in product(range(1, 33), range(2, 17)):
        logB = 63+64*logq; B = 1 << logB; J = (B**t-1)//(B-1)
        assert J.bit_count() == t and (J-2).bit_count() == logB+t-2 > logq
        count['literal_geometry_negative_sign_exclusions'] += 1
    for b in range(2, 15):
        for exponent in range(1, 100):
            assert (((1 << exponent)-1) % ((1 << b)-1) == 0) == (exponent % b == 0)
            count['dyadic_repunit_order_cases'] += 1
    for r, H in product(range(9, 33), (-1, 0, 1)):
        X = 1 << (2*r+1); beta = X-r-H
        assert beta > 2
        for delta in (0, 2):
            assert beta-delta > 0 and (1-delta)**2 == 1
            count['four_fiber_positive_slack_components'] += 1
    return dict(counts=dict(count), surviving_sign_cases=dict(survivors), negative_index_component=example,
                scope='Population, borrow, positive coordinate-map and repunit components only; this field example is not a complete compiled Pell zero.')


def guards():
    count = 0
    def reject(fn):
        nonlocal count
        try: fn()
        except (AssertionError, KeyError, TypeError, ValueError): count += 1
        else: raise AssertionError('malformed caller accepted')
    for key in forms():
        p = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        values = {n: 1 for n in p['parameters']+p['auxiliaries']}
        for field, value in [('source', p['source'][:-1]), ('comparisons', []), ('unit_factors', []),
                             ('projection', 'identity'), ('coupled_interfaces', []),
                             ('identical_positive_zero_set', True)]:
            for api in (checked, polynomial_source, degree_audit, ledger):
                reject(lambda field=field, value=value, api=api: api(dict(p, **{field: value})))
        for value in (1.0, True):
            changed = deepcopy(p)
            i = next(i for i, row in enumerate(changed['source']) if any(type(a) is int and a == 1 for a in row[2:]))
            row = list(changed['source'][i]); j = next(j for j in (2, 3) if type(row[j]) is int and row[j] == 1)
            row[j] = value; changed['source'][i] = tuple(row)
            for api in (checked, polynomial_source, ledger): reject(lambda api=api: api(changed))
            bad = dict(values); bad[next(iter(values))] = value
            for api in (evaluate, project_assignment, lift_assignment, offzero_correction): reject(lambda api=api: api(p, bad))
        changed = deepcopy(p); changed['source'][0] = list(changed['source'][0]); reject(lambda: checked(changed))
        changed = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2]); changed['source'].clear()
        assert exact_equal(p, _build(*key))
        for bad in ({}, dict(values, extra=1), list(values.items())):
            for api in (evaluate, project_assignment, lift_assignment, offzero_correction): reject(lambda api=api, bad=bad: api(p, bad))
        for delta in (True, 0.0, -2, 1, 4):
            reject(lambda delta=delta: lift_assignment(p, values, recoder_delta=delta))
            reject(lambda delta=delta: lift_assignment(p, values, history_delta=delta))
    for name in ('inline_initial', 'and_bounds', 'geometry_bounds'):
        for value in (1, 0, 1.0): reject(lambda name=name, value=value: build(**{name: value}))
    _build.cache_clear(); _canonical_parent.cache_clear()
    for key in forms():
        old = canonical_parent(*key); changed = deepcopy(old)
        i = next(i for i, row in enumerate(changed['source']) if row[0] == 'B')
        n, op, coefficient, rhs = changed['source'][i]
        changed['source'][i] = (n, op, coefficient+1, rhs)
        reject(lambda: rewrite(changed))
        old['source'].clear()
        clean = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        assert clean['coupled_parent_source'] == canonical_parent(*key)['source']
        for value in (1.0, True):
            changed = canonical_parent(*key)
            i = next(i for i, row in enumerate(changed['source']) if any(type(a) is int and a == 1 for a in row[2:]))
            row = list(changed['source'][i]); j = next(j for j in (2, 3) if type(row[j]) is int and row[j] == 1)
            row[j] = value; changed['source'][i] = tuple(row)
            reject(lambda: rewrite(changed))
    for args in ((1, True, True), (True, 1.0, True), (True, True, 0)):
        reject(lambda args=args: canonical_parent(*args))
    return count


def verify():
    records = []
    for key in forms():
        p = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        old = canonical_parent(*key); record = ledger(p)
        rows, out = polynomial_source(p); previous, _ = parent.polynomial_source(old)
        oldcount = Counter(op for n, op, a, b in previous)
        assert len(rows) == len(previous)-3
        assert record['polynomial']['multiplications'] == oldcount['*']
        assert record['polynomial']['additions_subtractions'] == oldcount['+']+oldcount['-']-3
        by = {n: (a, b) for n, op, a, b in rows}; seen = set(); todo = [out]
        while todo:
            n = todo.pop()
            if isinstance(n, str) and n in by and n not in seen: seen.add(n); todo.extend(by[n])
        assert seen == by.keys()
        record.update(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2],
                      source=rows, output=out, parameters=p['parameters'], auxiliaries=p['auxiliaries'],
                      comparisons=p['comparisons'], unit_factors=p['unit_factors'], unit_register=p['unit_register'],
                      source_sha256=hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest())
        records.append(record)
    return dict(status='PASS_GPCP_COUPLED_INDEX_UNITS754', parent_source_sha256=PARENT_SHA256,
                source_file_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                forms=records, source_audit=source_audit(), mathematical_audit=mathematical_audit(),
                rejected_callers=guards(),
                scope='Exactly four positive preimages over each positive zero of eight selected757 parents, with identity section, for every positive program parameter. Exact formal degree certificates. No complete enormous Pell fixture is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('status', 'forms')})
