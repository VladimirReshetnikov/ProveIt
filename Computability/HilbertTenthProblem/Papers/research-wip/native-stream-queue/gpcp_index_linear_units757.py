"""Fixed-target index/linear units in the complete positive GPCP source.

All six new signs are forced +1 locally, before either checksum or padding
sign is recovered.  Full supplied positive zero sets equal the selected
763 or 765 parent; no off-zero identity or fresh-witness projection is used.
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

import gpcp_first_padding_units763 as padding
import gpcp_upper_transport_unit765 as upper
import gpcp_shared_selectors774 as degrees_parent
import gpcp_normalized_strong_compiler as finalizer

PREFIXES = ('geo__', 'and__', 'hist__and__')
PARENTS = {763: padding, 765: upper}
PRIMES = (1000000007, 1000000009)
execute = upper.execute


def typed_key(value):
    return (type(value), tuple(typed_key(v) for v in value)) if type(value) is tuple else (type(value), value)


def exact_equal(a, b, seen=None):
    """Type-sensitive canonical equality, including historical tuple keys."""
    if type(a) is not type(b): return False
    if a is b: return True
    if seen is None: seen = set()
    if type(a) in (dict, list, tuple):
        pair = (id(a), id(b))
        if pair in seen: return True
        seen.add(pair)
    if type(a) is dict:
        ak = {typed_key(k): k for k in a}; bk = {typed_key(k): k for k in b}
        return ak.keys() == bk.keys() and all(exact_equal(a[ak[k]], b[bk[k]], seen) for k in ak)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact_equal(x, y, seen) for x, y in zip(a, b))
    return a == b


def options(parent_stage, inline_initial, and_bounds, geometry_bounds, index_units, linear_units):
    assert type(parent_stage) is int and parent_stage in PARENTS
    assert all(type(v) is bool for v in (inline_initial, and_bounds, geometry_bounds, index_units, linear_units))
    assert index_units or linear_units, 'at least one local conversion is required'
    return parent_stage, inline_initial, and_bounds, geometry_bounds, index_units, linear_units


@lru_cache(None)
def _canonical_parent(stage, inline, ands, geo):
    return PARENTS[stage].build(inline_initial=inline, and_bounds=ands, geometry_bounds=geo)


def canonical_parent(stage, inline, ands, geo):
    key = options(stage, inline, ands, geo, True, True)
    return deepcopy(_canonical_parent(*key[:4]))


def compact_parent(old):
    """Retain every current program/history interface; ancestry stays in its module."""
    keys = degrees_parent.ACTIVE + ('history_packet', 'and_bounds', 'geometry_bounds',
        'bound_unit_specs', 'history_upper_transport', 'upper_transport_unit', 'upper_transport_register',
        'first_padding_units', 'first_padding_interfaces', 'normalized_strong_factors', 'normalized_three_core')
    return {k: deepcopy(old[k]) for k in keys if k in old}


def rewrite(old, *, parent_stage=763, index_units=True, linear_units=True):
    assert type(old) is dict
    key = options(parent_stage, *(old.get(k) for k in ('inline_initial', 'and_bounds', 'geometry_bounds')),
                  index_units, linear_units)
    assert exact_equal(old, _canonical_parent(*key[:4])), 'complete canonical positive parent required'
    by = {n: (op, a, b) for n, op, a, b in old['source']}
    assert len(by) == len(old['source']) and old['comparisons'][-1] == (old['unit_register'], 1)
    changes = {}; extra = []; pairs = list(old['comparisons'][:-1])
    unit = old['unit_register']; factors = list(old['unit_factors']); interfaces = []
    for pre in PREFIXES:
        k, r1, target, K, U, V = [pre + n for n in ('R10b', 'r1', 'tr1', 'R11', 'H17', 'aux_u_rhs')]
        r = by[r1][1]
        expected = {r1: ('+', r, 1), target: ('+', r1, r),
            K: ('+', r1, pre+'hpm1'), U: ('-', pre+'jc', target),
            pre+'H2': ('*', U, U), V: ('-', pre+'of', pre+'R10a'),
            pre+'jc': ('*', pre+'j', pre+'R10a'), pre+'of': ('*', pre+'o', pre+'f'),
            pre+'hpm1': ('*', pre+'h', pre+'UM'),
            pre+'R16': ('*', pre+'A', pre+'normalized_strong_Q'),
            pre+'normalized_strong_Q': ('*', pre+'A', pre+'ic22'),
            pre+'f_square_minus_one': ('-', pre+'L16', pre+'normalized_strong_Q')}
        assert all(by.get(n) == row for n, row in expected.items())
        assert old['comparisons'].count((k, K)) == old['comparisons'].count((U, V)) == 1
        assert not any(K in (a, b) for n, op, a, b in old['source'])
        assert {n for n, op, a, b in old['source'] if U in (a, b)} == {pre+'H2'}
        assert {n for n, op, a, b in old['source'] if target in (a, b)} == {U}
        assert {n for n, op, a, b in old['source'] if r1 in (a, b)} == {K, target}
        assert not any(V in (a, b) for n, op, a, b in old['source'])
        interface = dict(prefix=pre, packed_index=r, first_pell=k, first_modulus=pre+'UM',
                         auxiliary_value=V, retained_normalized_strong=pre+'f_square_minus_one',
                         parent_index_comparison=(k, K), parent_linear_comparison=(U, V))
        if index_units:
            factor, total = pre+'index_unit', pre+'index_product'
            assert factor not in by and total not in by
            changes[K] = ('-', k, pre+'hpm1')
            extra.extend([(factor, '-', K, r), (total, '*', unit, factor)])
            unit = total; factors.append(factor); pairs.remove((k, K))
            interface.update(index_unit=factor, index_difference_register=K, index_formula='k-hXY-r')
        if linear_units:
            factor, total = pre+'linear_unit', pre+'linear_product'
            assert factor not in by and total not in by
            changes[target] = ('+', r1, r1)
            changes[U] = ('-', V, pre+'jc')
            changes[pre+'H2'] = ('*', V, V)
            extra.extend([(factor, '+', U, target), (total, '*', unit, factor)])
            unit = total; factors.append(factor); pairs.remove((U, V))
            interface.update(linear_unit=factor, shifted_target_register=target,
                             linear_difference_register=U, linear_formula='V-jc+2r+2',
                             target_uses='fixed packed r, never K')
        interfaces.append(interface)
    source = [(n, *changes.get(n, (op, a, b))) for n, op, a, b in old['source']] + extra
    source = degrees_parent.sorted_source(source, old['parameters'] + old['auxiliaries'])
    count = Counter(op for n, op, a, b in source)
    p = compact_parent(old)
    p.update(source=source, comparisons=pairs+[(unit, 1)], unit_factors=factors, unit_register=unit,
        operations=len(source), multiplications=count['*'], additions_subtractions=count['+']+count['-'],
        equations=len(pairs)+1, witnesses=old['witnesses'], parent_stage=parent_stage,
        index_units=index_units, linear_units=linear_units, index_linear_interfaces=interfaces,
        index_linear_parent_source=list(old['source']), index_linear_parent_comparisons=list(old['comparisons']),
        index_linear_parent_unit_register=old['unit_register'], index_linear_parent_unit_factors=list(old['unit_factors']),
        index_linear_changed_definitions=changes,
        identical_complete_integer_polynomial=False, identical_positive_zero_set=True,
        positive_zero_bijection=True, positive_zero_surjection=True,
        positive_zero_equality_scope='Full same-coordinate positive zeros for every positive program parameter, relative to the selected763/765 parent.',
        projection='Identity on supplied positive coordinates. All new fixed-target index/linear signs are forced+1 before inherited checksum/padding/history recovery.',
        positive_section='Identity on supplied positive zeros of the selected parent.')
    removed = 3 * (index_units + linear_units)
    assert p['operations'] == old['operations'] + 2*removed
    assert p['equations'] == old['equations'] - removed
    assert p['parameters'] == old['parameters'] and p['auxiliaries'] == old['auxiliaries']
    return p


@lru_cache(None)
def _build(stage, inline, ands, geo, index, linear):
    return rewrite(_canonical_parent(stage, inline, ands, geo), parent_stage=stage, index_units=index, linear_units=linear)


def build(*, parent_stage=763, inline_initial=True, and_bounds=True, geometry_bounds=True, index_units=True, linear_units=True):
    return deepcopy(_build(*options(parent_stage, inline_initial, and_bounds, geometry_bounds, index_units, linear_units)))


def checked(packet):
    assert type(packet) is dict
    key = options(*(packet.get(k) for k in ('parent_stage', 'inline_initial', 'and_bounds', 'geometry_bounds', 'index_units', 'linear_units')))
    assert exact_equal(packet, _build(*key)), 'complete type-sensitive canonical757 packet required'


def polynomial_source(packet=None):
    if packet is None: packet = build()
    checked(packet)
    return finalizer.polynomial_source(packet)


def degree_dictionary(packet=None):
    if packet is None: packet = build()
    rows, _ = polynomial_source(packet)
    return degrees_parent.raw_degrees(dict(packet, source=rows))


def leading_audit(packet, prime):
    assert type(prime) is int and prime in PRIMES
    rows, out = polynomial_source(packet); degree = degree_dictionary(packet)
    top = {n: i+2 for i, n in enumerate(packet['parameters']+packet['auxiliaries'])}
    for pre in PREFIXES: top[pre+'tau_gap'] = top[pre+'eta'] = top[pre+'zeta'] = 1
    for n, op, a, b in rows:
        da = degree[a] if isinstance(a, str) else 0; db = degree[b] if isinstance(b, str) else 0
        va = top[a] if isinstance(a, str) else a; vb = top[b] if isinstance(b, str) else b
        top[n] = (va*vb if op == '*' else (va if da == degree[n] else 0)
                  + (1 if op == '+' else -1)*(vb if db == degree[n] else 0)) % prime
        for pre in PREFIXES:
            if n != pre+'R15': continue
            d = lambda x: degree[pre+x]
            high = d('cam2') + d('gam')
            assert degree[n] == high > max(2*d('wn2'), d('wn2')+d('cam2'), d('wn2')+d('gam'),
                                                2*d('gam'), d('a4m5')+2*d('R10a'))
            # raw_degrees checks every literal row in this expanded identity.
            top[n] = 2*top[pre+'cam2']*top[pre+'gam'] % prime
    assert top[out] and all(top[f] for f in packet['unit_factors'])
    return dict(prime=prime, degree=degree[out], output_leader_value=top[out],
                factor_leader_values={f: top[f] for f in packet['unit_factors']})


def degree_audit(packet=None):
    if packet is None: packet = build()
    rows, out = polynomial_source(packet); d = degree_dictionary(packet)
    at = lambda n: d[n] if isinstance(n, str) else 0
    maximum = max(max(at(a), at(b)) for a, b in packet['comparisons'][:-1])
    assert d[out] == d[packet['unit_register']] + 2*maximum
    certificates = [leading_audit(packet, p) for p in PRIMES]
    return dict(exact_degree=d[out], propagated_upper_bound=d[out], unit_degree=d[packet['unit_register']],
                maximum_outer_degree=maximum,
                factor_degrees={f: d[f] for f in packet['unit_factors']},
                leading_certificates=certificates,
                assurance='Literal degree propagation with fully guarded three main-norm expansions; nonzero top homogeneous evaluations certify exactness before program specialization.')


def ledger(packet=None):
    if packet is None: packet = build()
    rows, out = polynomial_source(packet); c = Counter(op for n, op, a, b in rows)
    return dict(certificate={k: packet[k] for k in ('operations', 'multiplications', 'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(rows), multiplications=c['*'], additions_subtractions=c['+']+c['-'], output=out),
                degree=degree_audit(packet))


def forms():
    for stage in (763, 765):
        for inline, ands, geo in product((False, True), repeat=3):
            for index, linear in ((True, False), (False, True), (True, True)):
                yield stage, inline, ands, geo, index, linear


def source_audit(cases=12):
    count = Counter(); rng = random.Random(757763)
    for key in forms():
        p = deepcopy(_build(*key)); old = _canonical_parent(*key[:4])
        rows, out = polynomial_source(p); before, target = PARENTS[key[0]].polynomial_source(old)
        affected = set(p['index_linear_changed_definitions'])
        for n, op, a, b in old['source']:
            if a in affected or b in affected: affected.add(n)
        for case in range(cases):
            signed = case >= cases//2
            values = {n: rng.randrange(-2, 3) if signed else rng.randrange(1, 3)
                      for n in p['parameters']+p['auxiliaries']}
            if case % 4 == 0:
                values.update({f'hist__Shat{i}': 1 for i in range(57)})
                count['zero_selector_contexts'] += 1
            e = execute(rows, values); a = execute(before, values)
            assert all(e[n] == a[n] for n, op, u, v in old['source'] if n not in affected)
            corrected = {f: a[f] for f in old['unit_factors']}; removed = 0
            for pre in PREFIXES:
                if p['index_units']:
                    residual = a[pre+'R10b'] - a[pre+'R11']
                    assert e[pre+'index_unit'] == residual+1; removed += residual*residual
                if p['linear_units']:
                    residual = a[pre+'H17'] - a[pre+'aux_u_rhs']
                    assert e[pre+'linear_unit'] == 1-residual; removed += residual*residual
                    corrected[pre+'P17'] += a[pre+'R16']*(a[pre+'aux_u_rhs']**2-a[pre+'H17']**2)
                assert e[pre+'P17'] == corrected[pre+'P17']
            assert all(e[f] == v for f, v in corrected.items())
            extra_factors = [f for f in p['unit_factors'] if f not in old['unit_factors']]
            oldW = prod(a[f] for f in old['unit_factors'])
            newW = prod(corrected.values())*prod(e[f] for f in extra_factors)
            get = lambda env, n: env[n] if isinstance(n, str) else n
            S = sum((get(e, u)-get(e, v))**2 for u, v in p['comparisons'][:-1])
            oldS = sum((get(a, u)-get(a, v))**2 for u, v in old['comparisons'][:-1])
            assert oldS == S+removed
            assert e[p['unit_register']] == newW and a[old['unit_register']] == oldW
            assert e[out] == newW*(1+S)-1 and a[target] == oldW*(1+S+removed)-1
            assert e[out]-a[target] == (newW-oldW)*(1+S)-oldW*removed
            count['complete_register_factor_corrections'] += 1
            count['complete_output_corrections'] += 1
            count['signed_cases'] += signed
    return dict(count)


def pell(A, n):
    x, y = 1, 0
    for _ in range(n): x, y = A*x+(A*A-1)*y, x+A*y
    return x, y


def mathematical_audit():
    count = Counter()
    for X, Y in product((2, 3, 5, 8), (2, 3, 6, 16)):
        A = Y*(X+1)+2; P0 = 2*X*Y*Y+1; Q = 2*A*A-1
        assert Q > P0 > A and 2*A > Y+1
        for r in range(3, 11):
            for epsilon, lam in product((-1, 1), repeat=2):
                n, p = r+epsilon, 2*r+2-lam
                k = pell(P0, n)[1]
                assert pell(A, 2*n)[1] == 2*A*pell(Q, n)[1] > k*(Y+1)
                if (epsilon, lam) != (1, 1):
                    assert p >= 2*n+1 and pell(A, p)[1] > k*(Y+1)
                    count['wrong_sign_duplication_exclusions'] += 1
                else: assert p == 2*n-1
                count['fixed_target_sign_cases'] += 1
    # The weakest actual bootstrap uses n>=r-1, p>=r, never a recovered sign.
    for Y in (6, 16, 48):
        for r in (9, 48, 4369, 2**127):
            X = r; A = Y*(X+1)+2; E = X*Y
            assert E > 2*r+3 and Y*(r-1) > 2*(2*r+3)
            assert (2*A-1)**8 > A**8 > A*(A*A-1)**2
            count['weak_X_equals_r_and_n_equals_r_minus_one_margins'] += 1
    # Complete normalized strong equation, not an assumed c|m shortcut.
    for A in range(2, 8):
        for p in range(1, 7):
            d, c = pell(A, p)
            for m in range(1, 65):
                f, y = pell(A, m)
                if y % (c*c) == 0:
                    assert m % (p*c) == 0
                    count['normalized_strong_pc_divisibility_cases'] += 1
    # Actual signed padding/checksum residue branches preserve the weak X bound.
    for stage in (763, 765):
        for checksum, sign in product((-1, 1), repeat=2):
            if stage == 765 and sign != 1: continue
            low = ((-checksum-(5-sign)-2-8) % 16, 5-sign, 2, 8)
            assert low[0] % 2 == 1 and 0 < low[0] < 16
            for q in (16, 32, 64, 128):
                total = (q-checksum-sum(low))//16
                if total < 0: continue
                fields = (low[0]+16*total, *low[1:])
                assert sum(fields) == q-checksum and all(v > 0 for v in fields)
                r = sum(v*q**j for j, v in enumerate(fields)); X = q*((r+q-1)//q); Y = 3*q
                assert X > r >= 9 and X*Y > 2*r+3 and Y*(r-1) > 2*(2*r+3)
                count['signed_AND_bound_cones'] += 1
    for q in (2, 3, 5, 16):
        B = 2**63*q**64; r = X = B; Y = 3*q
        assert r >= 2**127 and r > q and X*Y > 2*r+3 and Y*(r-1) > 2*(2*r+3)
        count['weak_geometry_bound_cones'] += 1
    return dict(count, scope='Exact component tests only; no complete enormous Pell witness is materialized.')


def guards():
    count = 0
    def reject(fn):
        nonlocal count
        try: fn()
        except (AssertionError, KeyError, TypeError, ValueError): count += 1
        else: raise AssertionError('malformed caller accepted')
    for key in forms():
        p = deepcopy(_build(*key))
        for name, value in [('source', p['source'][:-1]), ('comparisons', []), ('unit_factors', []),
                            ('positive_zero_equality_scope', 'bad'), ('index_linear_interfaces', [])]:
            for api in (checked, polynomial_source, degree_audit, ledger):
                reject(lambda name=name, value=value, api=api: api(dict(p, **{name: value})))
        mutated = deepcopy(p); mutated['source'][0] = list(mutated['source'][0])
        reject(lambda: checked(mutated))
        for value in (1.0, True):
            mutated = deepcopy(p)
            i = next(i for i, row in enumerate(mutated['source']) if any(type(a) is int and a == 1 for a in row[2:]))
            row = list(mutated['source'][i]); j = next(j for j in (2, 3) if type(row[j]) is int and row[j] == 1)
            row[j] = value; mutated['source'][i] = tuple(row)
            reject(lambda: checked(mutated))
        damaged = build(parent_stage=key[0], inline_initial=key[1], and_bounds=key[2], geometry_bounds=key[3], index_units=key[4], linear_units=key[5])
        damaged['source'].clear()
        assert exact_equal(_build(*key), p)
    for key in ('inline_initial', 'and_bounds', 'geometry_bounds', 'index_units', 'linear_units'):
        reject(lambda key=key: build(**{key: 1}))
    for stage in (True, 763.0, 764): reject(lambda stage=stage: build(parent_stage=stage))
    reject(lambda: build(index_units=False, linear_units=False))
    # Exercise a public parent mutation before the successor cache is populated.
    # A public accessor must never hand out the private canonical guard reference.
    _build.cache_clear()
    for stage in (763, 765):
        damaged = canonical_parent(stage, True, True, True)
        i = next(i for i, row in enumerate(damaged['source']) if row[0] == 'B')
        name, op, value, rhs = damaged['source'][i]
        assert type(value) is int
        damaged['source'][i] = (name, op, value+1, rhs)
        reject(lambda: rewrite(damaged, parent_stage=stage))
        clean = build(parent_stage=stage)
        assert clean['index_linear_parent_source'] == _canonical_parent(stage, True, True, True)['source']
        assert exact_equal(canonical_parent(stage, True, True, True), _canonical_parent(stage, True, True, True))
        old = canonical_parent(stage, True, True, True)
        for name, value in [('source', old['source'][:-1]), ('history_packet', {}), ('projection', 'bad')]:
            reject(lambda name=name, value=value, stage=stage: rewrite(dict(old, **{name: value}), parent_stage=stage))
        for value in (1.0, True):
            damaged = dict(old); rows = list(old['source'])
            i = next(i for i, row in enumerate(rows) if any(type(a) is int and a == 1 for a in row[2:]))
            row = list(rows[i]); j = next(j for j in (2, 3) if type(row[j]) is int and row[j] == 1)
            row[j] = value; rows[i] = tuple(row); damaged['source'] = rows
            reject(lambda: rewrite(damaged, parent_stage=stage))
    for args in ((763.0, True, True, True), (True, True, True, True), (763, 1, True, True)):
        reject(lambda args=args: canonical_parent(*args))
    return count


def verify():
    records = []
    for key in forms():
        p = deepcopy(_build(*key)); old = _canonical_parent(*key[:4]); record = ledger(p)
        rows, out = polynomial_source(p); previous, _ = PARENTS[key[0]].polynomial_source(old)
        changes = 3*(key[4]+key[5]); oldcount = Counter(op for n, op, a, b in previous)
        assert len(rows) == len(previous)-changes
        assert record['polynomial']['multiplications'] == oldcount['*']
        assert record['polynomial']['additions_subtractions'] == oldcount['+']+oldcount['-']-changes
        by = {n: (a, b) for n, op, a, b in rows}; seen = set(); todo = [out]
        while todo:
            n = todo.pop()
            if isinstance(n, str) and n in by and n not in seen: seen.add(n); todo.extend(by[n])
        assert seen == by.keys()
        record.update(parent_stage=key[0], inline_initial=key[1], and_bounds=key[2], geometry_bounds=key[3],
                      index_units=key[4], linear_units=key[5], source=rows, output=out,
                      parameters=p['parameters'], auxiliaries=p['auxiliaries'], comparisons=p['comparisons'],
                      unit_factors=p['unit_factors'], unit_register=p['unit_register'],
                      source_sha256=hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest())
        records.append(record)
    return dict(status='PASS_GPCP_FIXED_TARGET_INDEX_LINEAR_UNITS757', forms=records,
                source_audit=source_audit(), mathematical_audit=mathematical_audit(), rejected_callers=guards(),
                scope='Same full positive zero sets on identical supplied coordinates for both selected763/765 parents and all positive program values. Exact formal degrees, no off-zero polynomial identity, no complete large Pell fixtures.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('status', 'forms')})
