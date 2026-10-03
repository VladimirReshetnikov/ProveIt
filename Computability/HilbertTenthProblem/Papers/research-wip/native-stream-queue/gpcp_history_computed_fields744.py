"""Compute only the history AND truth fields in the complete positive GPCP source.

The restored graph is polynomially identical over all signed integers.
Positive zeros biject with the checksum-positive history slice of754;
normalization maps all754 positive zeros onto that slice. No recoder erasure.
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

import gpcp_coupled_index_units754 as parent

PARENT_SHA256 = '80c5f06ef5ec43975369ed2f9737fdf0d75b44e5abba4c24e19a2bc4fba1f9e3'
PRE = 'hist__and__'
ERASED_FIELDS = tuple(PRE+x for x in ('F0', 'F1', 'F2'))
PREFIXES = parent.PREFIXES
PRIMES = parent.PRIMES
exact_equal = parent.exact_equal
execute = parent.parent.execute
degrees_parent = parent.parent.degrees_parent


def flags(inline_initial, and_bounds, geometry_bounds):
    assert all(type(v) is bool for v in (inline_initial, and_bounds, geometry_bounds))
    return inline_initial, and_bounds, geometry_bounds


def parent_hash_guard():
    assert hashlib.sha256(Path(parent.__file__).read_bytes()).hexdigest() == PARENT_SHA256
    parent.parent_hash_guard()


@lru_cache(None)
def _canonical_parent(inline, ands, geo):
    return parent.build(inline_initial=inline, and_bounds=ands, geometry_bounds=geo)


def canonical_parent(inline_initial=True, and_bounds=True, geometry_bounds=True):
    key = flags(inline_initial, and_bounds, geometry_bounds)
    parent_hash_guard()
    return deepcopy(_canonical_parent(*key))


def rewrite(old):
    assert type(old) is dict
    key = flags(*(old.get(k) for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    parent_hash_guard()
    assert exact_equal(old, _canonical_parent(*key)), 'complete exact-type canonical754 parent required'
    by = {n: (op, a, b) for n, op, a, b in old['source']}
    assert len(by) == len(old['source'])
    consumers = lambda x: {n for n, op, a, b in old['source'] if x in (a, b)}
    expected = {
        'shared_sum02': ('+', PRE+'F0', PRE+'F2'),
        'input_A': ('+', PRE+'F1', PRE+'F3'),
        'input_B': ('+', PRE+'F2', PRE+'F3'),
        'bs_Q': ('+', PRE+'shared_sum02', PRE+'input_A'),
        'bs_q': ('-', PRE+'q', PRE+'bs_Q'),
        'bs_p0': ('*', PRE+'q', PRE+'F3'),
        'bs_p1': ('+', PRE+'F2', PRE+'bs_p0'),
        'bs_p2': ('*', PRE+'q', PRE+'bs_p1'),
        'bs_p3': ('+', PRE+'F1', PRE+'bs_p2'),
        'bs_p4': ('*', PRE+'q', PRE+'bs_p3'),
        'bs_packed': ('+', PRE+'F0', PRE+'bs_p4'),
        'first_padding_unit': ('-', PRE+'padded_A', PRE+'input_A'),
        'first_padding_product': ('*', 'and__first_padding_product', PRE+'first_padding_unit'),
        'padded_A': ('+', PRE+'scaled_A', 13),
        'padded_B': ('+', PRE+'scaled_B', 10),
        'F3': ('+', PRE+'scaled_Z', 8),
        'q': ('*', 16, 'hist__P69__550'),
        'bs_X_bound': ('+', PRE+'bs_packed', PRE+'bound_beta'),
        'index_unit': ('-', PRE+'R11', PRE+'bs_packed'),
        'tr1': ('+', PRE+'R11', PRE+'R11'),
    }
    assert all(by.get(PRE+n) == row for n, row in expected.items())
    assert by['both_checksum_units'] == ('*', PRE+'normalized_all_units', PRE+'bs_q')
    for name, suffixes in {'F0': ('shared_sum02', 'bs_packed'),
                           'F1': ('input_A', 'bs_p3'),
                           'F2': ('shared_sum02', 'input_B', 'bs_p1'),
                           'bound_beta': ('bs_X_bound',)}.items():
        assert consumers(PRE+name) == {PRE+s for s in suffixes}
    assert consumers(PRE+'bs_packed') == {PRE+'bs_X_bound', PRE+'index_unit'}
    assert set(ERASED_FIELDS) <= set(old['auxiliaries'])
    assert old['comparisons'].count((PRE+'input_B', PRE+'padded_B')) == 1
    assert old['comparisons'][-1] == (old['unit_register'], 1)
    hp = old['history_packet']
    assert old['tiles'] == hp['tiles'] == 57 and hp['selected_products'] == 8
    assert hp['K'] == 131072 and hp['scale_exponent'] == 69
    assert hp['region_exponents'] == dict(controller=8, range=65, top=67)
    assert len(hp['groups_U']) == len(hp['groups_V']) == 4
    for group in hp['groups_U']+hp['groups_V']:
        assert len(group['tiles']) == len(set(group['tiles']))
        assert all(0 <= i < 57 for i in group['tiles'])
    for name, row in {
        'hist__height_sum__0': ('+', 'Ufinal', 'input_bottom' if key[0] else 'Vinitial'),
        'hist__height_sum__1': ('+', 'Vfinal', 'hist__height_sum__0'),
        'hist__height_sum__2': ('+', 'hist__height_slack', 'hist__height_sum__1'),
        'hist__B__3': ('*', 'hist__height_sum__2', 131072),
        'hist__P__63': ('+', 'hist__P_product__62', 1),
        'history_global_unit': ('-', 'hist__P__63', 'hist__global_lhs__73'),
    }.items(): assert by[name] == row
    # The erased truth fields are private; program, words, layout and history
    # exports are kept in full, not inferred from a small interface summary.
    active = {k: old[k] for k in degrees_parent.ACTIVE+('history_packet',)
              if k not in ('auxiliaries', 'comparisons', 'unit_factors')}
    assert not set(ERASED_FIELDS) & degrees_parent.leaves(active)
    deleted = {PRE+n for n in ('shared_sum02', 'input_A', 'input_B', 'bs_Q', 'bs_q',
               'bs_p0', 'bs_p1', 'bs_p2', 'bs_p3', 'bs_p4', 'bs_packed',
               'first_padding_unit', 'first_padding_product')} | {'both_checksum_units'}
    aliases = {'both_checksum_units': PRE+'normalized_all_units',
               PRE+'first_padding_product': 'and__first_padding_product'}
    sub = lambda n: aliases.get(n, n)
    rows = [(n, op, sub(a), sub(b)) for n, op, a, b in old['source'] if n not in deleted]
    qm, qp, v, u, w, S = (PRE+'computed_'+n for n in ('qm', 'qp', 'v', 'u', 'w', 'S'))
    rows += [(qm, '-', PRE+'q', 1), (qp, '+', PRE+'q', 1), (v, '*', qm, PRE+'F3'),
             (u, '+', PRE+'padded_B', v), (w, '*', qp, u),
             (S, '+', PRE+'padded_A', w), (PRE+'bs_packed', '*', qm, S)]
    aux = [n for n in old['auxiliaries'] if n not in ERASED_FIELDS]
    rows = degrees_parent.sorted_source(rows, old['parameters']+aux)
    pairs = [(sub(a), sub(b)) for a, b in old['comparisons']
             if (a, b) != (PRE+'input_B', PRE+'padded_B')]
    removed_factors = (PRE+'bs_q', PRE+'first_padding_unit')
    counts = Counter(op for n, op, a, b in rows)
    p = parent.parent.compact_parent(old)
    p['first_padding_units'] = [n for n in p['first_padding_units'] if n not in removed_factors]
    p['first_padding_interfaces'] = [i for i in p['first_padding_interfaces'] if i['prefix'] != PRE]
    p.update(source=rows, operations=len(rows), multiplications=counts['*'],
             additions_subtractions=counts['+']+counts['-'], comparisons=pairs,
             equations=len(pairs), auxiliaries=aux, witnesses=len(aux),
             unit_factors=[f for f in old['unit_factors'] if f not in removed_factors],
             parent_stage=754, history_computed_fields=True, recoder_computed_fields=False,
             erased_fields=list(ERASED_FIELDS), removed_unit_factors=list(removed_factors),
             erased_source_rows=sorted(deleted-{PRE+'bs_packed'}),
             parent_source=list(old['source']), parent_comparisons=list(old['comparisons']),
             parent_unit_factors=list(old['unit_factors']), parent_auxiliaries=list(old['auxiliaries']),
             parent_unit_register=old['unit_register'], parent_sha256=PARENT_SHA256,
             computed_interface=dict(prefix=PRE, q=PRE+'q', padded_A=PRE+'padded_A',
                 padded_B=PRE+'padded_B', F3=PRE+'F3', packed_index=PRE+'bs_packed',
                 restoration=['q-(padded_A-1)-padded_B+F3-1', 'padded_A-1-F3', 'padded_B-F3']),
             positive_restoration_bijection_to_parent_history_checksum_positive_slice=True,
             parent_positive_projection_surjective=True, parent_positive_projection_fiber_cardinality=2,
             same_supplied_coordinate_set=False, identical_polynomial_on_restored_graph=True,
             supplied_domain='positive integers; signed integers accepted only for formal graph algebra',
             projection='Normalize parent history F0+=checksum-1, beta+=1-checksum, then erase history F0,F1,F2.',
             restoration='Restore only history F0,F1,F2 from q,padded_A,padded_B,F3; every retained supplied coordinate is unchanged.',
             positive_relation_scope='Bijection with the history-checksum+1 parent754 slice; exactly two parent positive zeros project to each child positive zero. Recoder sign branch retained. Every positive program parameter choice; existence is not asserted for every ordinary input.')
    assert p['operations'] == old['operations']-7
    assert p['multiplications'] == old['multiplications']-2
    assert p['additions_subtractions'] == old['additions_subtractions']-5
    assert p['witnesses'] == old['witnesses']-3 and p['equations'] == old['equations']-1
    current = {k: p[k] for k in degrees_parent.ACTIVE+('history_packet', 'first_padding_units', 'first_padding_interfaces')}
    assert not set(ERASED_FIELDS) & degrees_parent.leaves(current)
    assert not (deleted-{PRE+'bs_packed'}) & degrees_parent.leaves(current)
    assert all(k not in p for k in ('coupled_interfaces', 'positive_projection_fiber_cardinality', 'coupled_parent_source'))
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
    assert exact_equal(packet, _build(*key)), 'complete exact-type canonical744 packet required'


def polynomial_source(packet=None):
    if packet is None: packet = build()
    checked(packet)
    return parent.parent.finalizer.polynomial_source(packet)


def checked_values(packet, values, *, parent_values=False):
    checked(packet)
    assert type(parent_values) is bool
    aux = packet['parent_auxiliaries'] if parent_values else packet['auxiliaries']
    assert type(values) is dict and set(values) == set(packet['parameters']+aux)
    assert all(type(n) is str and type(v) is int for n, v in values.items())


def evaluate(packet, values):
    checked_values(packet, values)
    rows, out = polynomial_source(packet)
    return execute(rows, values)[out]


def restore_assignment(packet, values):
    """Formal graph over integers; restored fields are positive at positive zeros."""
    checked_values(packet, values)
    e = execute(packet['source'], values)
    A, C, Z, q = (e[PRE+'padded_A']-1, e[PRE+'padded_B'], e[PRE+'F3'], e[PRE+'q'])
    return dict(values, **dict(zip(ERASED_FIELDS, (q-A-C+Z-1, A-Z, C-Z))))


def normalize_parent_assignment(packet, values):
    """Formal checksum normalization; preserves positive parent zeros."""
    checked_values(packet, values, parent_values=True)
    e = execute(packet['parent_source'], values); C = e[PRE+'bs_q']
    mapped = dict(values)
    mapped[PRE+'F0'] += C-1
    mapped[PRE+'bound_beta'] += 1-C
    return mapped


def project_assignment(packet, values):
    """Normalize a parent tuple and erase only the three history fields."""
    mapped = normalize_parent_assignment(packet, values)
    return {n: v for n, v in mapped.items() if n not in ERASED_FIELDS}


def lift_parent_assignment(packet, values, *, history_delta=0):
    """Two formal lifts; on positive child zeros both are positive parent zeros."""
    assert type(history_delta) is int and history_delta in (0, 2)
    restored = restore_assignment(packet, values)
    restored[PRE+'F0'] += history_delta
    restored[PRE+'bound_beta'] -= history_delta
    return restored


def offzero_identity(packet, values):
    """Compare every retained residual/factor and both full output schedules."""
    checked_values(packet, values)
    old = canonical_parent(*(packet[k] for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    rows, out = polynomial_source(packet); before, target = parent.polynomial_source(old)
    e = execute(rows, values); restored = restore_assignment(packet, values); past = execute(before, restored)
    assert all(past[f] == 1 for f in packet['removed_unit_factors'])
    assert past[PRE+'input_B'] == past[PRE+'padded_B']
    assert past[PRE+'bs_packed'] == e[PRE+'bs_packed']
    assert all(past[f] == e[f] for f in packet['unit_factors'])
    at = lambda env, n: env[n] if isinstance(n, str) else n
    retained = [at(e, a)-at(e, b) for a, b in packet['comparisons'][:-1]]
    original = [at(past, a)-at(past, b) for a, b in old['comparisons'][:-1]
                if (a, b) != (PRE+'input_B', PRE+'padded_B')]
    assert retained == original
    W = prod(e[f] for f in packet['unit_factors']); S = sum(r*r for r in retained)
    assert e[out] == past[target] == W*(1+S)-1
    assert {n: restored[n] for n in values} == values
    return dict(child_output=e[out], restored_parent_output=past[target], unit_product=W, retained_sos=S)


def normalization_correction(packet, values):
    """Full signed off-zero correction for history checksum normalization."""
    checked_values(packet, values, parent_values=True)
    old = canonical_parent(*(packet[k] for k in ('inline_initial', 'and_bounds', 'geometry_bounds')))
    rows, out = parent.polynomial_source(old)
    e = execute(rows, values); norm = normalize_parent_assignment(packet, values); after = execute(rows, norm)
    C, N = e[PRE+'bs_q'], e[PRE+'index_unit']
    assert after[PRE+'bs_q'] == 1 and after[PRE+'index_unit'] == N-C+1
    common_factors = [f for f in old['unit_factors'] if f not in (PRE+'bs_q', PRE+'index_unit')]
    assert all(after[f] == e[f] for f in common_factors)
    at = lambda env, n: env[n] if isinstance(n, str) else n
    residuals = [at(e, a)-at(e, b) for a, b in old['comparisons'][:-1]]
    assert residuals == [at(after, a)-at(after, b) for a, b in old['comparisons'][:-1]]
    common = prod(e[f] for f in common_factors); S = sum(r*r for r in residuals)
    correction = common*((N-C+1)-C*N)*(1+S)
    assert after[out]-e[out] == correction
    return dict(parent_output=e[out], normalized_parent_output=after[out], correction=correction)


def degree_dictionary(packet=None):
    if packet is None: packet = build()
    rows, _ = polynomial_source(packet)
    return degrees_parent.raw_degrees(dict(packet, source=rows))


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
    rng = random.Random(744754); count = Counter(); digest = hashlib.sha256()
    for key in forms():
        p = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        for case in range(cases):
            signed = case >= cases//2
            values = {n: rng.randrange(-2, 3) if signed else rng.randrange(1, 3)
                      for n in p['parameters']+p['auxiliaries']}
            if case % 4 == 0:
                values.update({f'hist__Shat{i}': 1 for i in range(57)})
                count['zero_selector_contexts'] += 1
            result = offzero_identity(p, values)
            digest.update(json.dumps({k: v % PRIMES[0] for k, v in result.items()}, sort_keys=True).encode())
            count['complete_signed_graph_identities'] += 1; count['signed_cases'] += signed
            restored = restore_assignment(p, values)
            assert project_assignment(p, restored) == values
            count['formal_graph_projection_roundtrips'] += 1
            for delta in (0, 2):
                lifted = lift_parent_assignment(p, values, history_delta=delta)
                assert project_assignment(p, lifted) == values
                count['formal_two_lift_projection_roundtrips'] += 1
            arbitrary = dict(restored)
            for name in ERASED_FIELDS: arbitrary[name] = rng.randrange(-3, 4)
            correction = normalization_correction(p, arbitrary)
            digest.update(str(correction['correction'] % PRIMES[0]).encode())
            count['complete_normalization_corrections'] += 1
    return dict(count, modular_result_digest=digest.hexdigest(),
                scope='Both full polynomial schedules executed on bounded signed and positive off-zero tuples; no enormous full Pell zero is materialized.')


def cone_audit(cases=64):
    """Literal weak-global fixtures; no Pell norms, AND typing or history equations."""
    rng = random.Random(74467); count = Counter(); minima = None
    for key in forms():
        p = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        by = {n: (o, a, b) for n, o, a, b in p['source']}
        want = {'hist__P__63', 'hist__B__3', 'hist__joined_H__539',
                'hist__joined_M__545', 'hist__joined_Z__546', 'history_global_unit'}
        todo = list(want)
        while todo:
            n = todo.pop()
            if n not in by: continue
            for atom in by[n][1:]:
                if isinstance(atom, str) and atom not in want: want.add(atom); todo.append(atom)
        scalar = [row for row in p['source'] if row[0] in want]
        ports = ['hist__H_U', 'hist__H_V']+[f'hist__{side}hat{i}' for side in ('ZU', 'ZV') for i in range(4)]
        for i in range(cases):
            values = {n: 1 for n in p['parameters']+p['auxiliaries']}
            for j in range(57): values[f'hist__Shat{j}'] = 1+rng.randrange(3)
            if i % 8 == 0: values.update({f'hist__Shat{j}': 1+int(j == 0) for j in range(57)})
            e = execute(scalar, values); P = e['hist__P__63']
            if i % 8 == 0:
                values['hist__H_U'] = P-9; sign = -1
                count['J1_P_equals_B_negative_global_boundary'] += 1
            else:
                for port in ports: values[port] = rng.randrange(1, 1001)
                sign = (-1, 1)[i % 2]
            values['hist__global_bound'] = P-sum(values[n] for n in ports)-sign
            assert values['hist__global_bound'] > 0
            e = execute(scalar, values); B = e['hist__B__3']
            H, M, Z = (e[n] for n in ('hist__joined_H__539', 'hist__joined_M__545', 'hist__joined_Z__546'))
            T, N = P**67, P**69
            assert e['history_global_unit'] == sign and P >= B >= 524288
            assert 0 <= H-B*T < T and 0 <= M-(B-1)*T < T and 0 <= Z < T
            fields = (16*(N-H-M+Z)-15, 16*(H-Z)+4, 16*(M-Z)+2, 16*Z+8)
            assert min(fields) > 0 and sum(fields) == 16*N-1
            assert tuple(f % 16 for f in fields) == (1, 4, 2, 8)
            count['literal_pretyping_history_cones'] += 1
            minima = min(fields) if minima is None else min(minima, min(fields))
    # The paired-history branch lift has positive beta independently of recoder.
    for r, H in product(range(9, 40), (-1, 0, 1)):
        beta = (1 << (2*r+1))-r-H
        assert beta > 2 and beta-2 > 0
        count['positive_two_fiber_slack_components'] += 1
    return dict(counts=dict(count), least_observed_truth_field=minima,
                scope='Complete actual scalar dependency slices and component slack checks only; no AND typing is assumed in the cone and no complete positive Pell zero is claimed.')


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
        oldvalues = restore_assignment(p, values)
        for field, value in [('source', p['source'][:-1]), ('comparisons', []), ('unit_factors', []),
                             ('projection', 'identity'), ('history_packet', {}),
                             ('parent_positive_projection_fiber_cardinality', 4), ('recoder_computed_fields', True)]:
            changed = dict(p, **{field: value})
            for api in (checked, polynomial_source, degree_audit, ledger): reject(lambda api=api: api(changed))
        for value in (1.0, True):
            changed = deepcopy(p)
            i = next(i for i, row in enumerate(changed['source']) if any(type(a) is int and a == 1 for a in row[2:]))
            row = list(changed['source'][i]); j = next(j for j in (2, 3) if type(row[j]) is int and row[j] == 1)
            row[j] = value; changed['source'][i] = tuple(row)
            for api in (checked, polynomial_source, ledger): reject(lambda api=api: api(changed))
            # Numerically equal coefficients cannot bypass the exact guard,
            # including endpoints at which a float evaluation would overflow.
            huge = dict(values); huge['x'] = 10**400
            reject(lambda: evaluate(changed, huge))
            for api in (evaluate, restore_assignment, lift_parent_assignment, offzero_identity):
                bad = dict(values); bad[next(iter(bad))] = value
                reject(lambda api=api, bad=bad: api(p, bad))
            for api in (normalize_parent_assignment, project_assignment, normalization_correction):
                bad = dict(oldvalues); bad[next(iter(bad))] = value
                reject(lambda api=api, bad=bad: api(p, bad))
        for api in (evaluate, restore_assignment, lift_parent_assignment, offzero_identity):
            for bad in ({}, dict(values, extra=1), list(values.items()), oldvalues): reject(lambda api=api, bad=bad: api(p, bad))
        for api in (normalize_parent_assignment, project_assignment, normalization_correction):
            for bad in ({}, dict(oldvalues, extra=1), list(oldvalues.items()), values): reject(lambda api=api, bad=bad: api(p, bad))
        for delta in (True, 0.0, -2, 1, 4): reject(lambda delta=delta: lift_parent_assignment(p, values, history_delta=delta))
        for prime in (True, float(PRIMES[0]), 7): reject(lambda prime=prime: leading_audit(p, prime))
        changed = deepcopy(p); changed['source'][0] = list(changed['source'][0]); reject(lambda: checked(changed))
        public = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        public['history_packet'].clear(); public['source'].clear()
        assert exact_equal(p, _build(*key))
    for name in ('inline_initial', 'and_bounds', 'geometry_bounds'):
        for value in (1, 0, 1.0): reject(lambda name=name, value=value: build(**{name: value}))
    _build.cache_clear(); _canonical_parent.cache_clear()
    for key in forms():
        old = canonical_parent(*key); changed = deepcopy(old)
        i = next(i for i, row in enumerate(changed['source']) if row[0] == 'B')
        n, op, coefficient, rhs = changed['source'][i]
        changed['source'][i] = (n, op, coefficient+1, rhs); reject(lambda: rewrite(changed))
        old['source'].clear(); old['history_packet'].clear()
        clean = build(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2])
        assert clean['parent_source'] == canonical_parent(*key)['source']
        for value in (1.0, True):
            changed = canonical_parent(*key); changed['witnesses'] = value
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
        assert len(rows) == len(previous)-10
        assert record['polynomial']['multiplications'] == oldcount['*']-3
        assert record['polynomial']['additions_subtractions'] == oldcount['+']+oldcount['-']-7
        by = {n: (a, b) for n, op, a, b in rows}; seen = set(); todo = [out]
        while todo:
            n = todo.pop()
            if isinstance(n, str) and n in by and n not in seen: seen.add(n); todo.extend(by[n])
        assert seen == by.keys()
        assert set(p['parameters']+p['auxiliaries']) <= degrees_parent.leaves(rows)
        record.update(inline_initial=key[0], and_bounds=key[1], geometry_bounds=key[2],
                      source=rows, output=out, parameters=p['parameters'], auxiliaries=p['auxiliaries'],
                      comparisons=p['comparisons'], unit_factors=p['unit_factors'], unit_register=p['unit_register'],
                      restoration=p['computed_interface'],
                      source_sha256=hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest())
        records.append(record)
    return dict(status='PASS_GPCP_HISTORY_COMPUTED_FIELDS744', parent_source_sha256=PARENT_SHA256,
                source_file_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                forms=records, source_audit=source_audit(), cone_audit=cone_audit(), rejected_callers=guards(),
                scope='Positive history-checksum-slice bijection and two-to-one parent normalization for all eight754 forms. Exact signed restored-graph identity and formal degrees. Recoder truth fields retained; no complete enormous Pell fixture or improvement to the separate87-operation universal bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('status', 'forms')})
