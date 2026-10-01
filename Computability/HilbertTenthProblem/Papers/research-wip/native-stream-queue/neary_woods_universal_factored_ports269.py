"""Exact port factorization of the complete computed-fields U9 polynomial.

The supplied coordinates and complete polynomial are unchanged. Removed
internal fields are restored diagnostically, not paid as unused gates.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_computed_ports275 as parent

compiler = parent.compiler
units = parent.units
execute = parent.execute
SORT = parent.parent.parent.parent.sort_source


def leaves(value):
    if isinstance(value, str):
        return {value}
    if isinstance(value, dict):
        value = value.values()
    elif not isinstance(value, (list, tuple)):
        return set()
    return set().union(*(leaves(v) for v in value))


def rewrite(old, *, fold_affine=True):
    assert old['computed_ports_mode'] == 'all'
    assert not old.get('factored_native_pack')
    compiler.check_source(old)
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    expected = {
        'and__F1': ('-', 'and__padded_A', 'and__F3'),
        'and__F2': ('-', 'and__padded_B', 'and__F3'),
        'computed_ports_remaining': ('-', 'and__q', 'and__padded_A'),
        'computed_ports_before_one': ('-', 'computed_ports_remaining', 'and__F2'),
        'and__F0': ('-', 'computed_ports_before_one', 1),
        'and__bs_p0': ('*', 'and__q', 'and__F3'),
        'and__bs_p1': ('+', 'and__F2', 'and__bs_p0'),
        'and__bs_p2': ('*', 'and__q', 'and__bs_p1'),
        'and__bs_p3': ('+', 'and__F1', 'and__bs_p2'),
        'and__bs_p4': ('*', 'and__q', 'and__bs_p3'),
        'and__bs_packed': ('+', 'and__F0', 'and__bs_p4'),
    }
    extra = {}
    if fold_affine:
        extra = {
            'fusion_low_padded_A': ('+', 'joint_A_sum', 12),
            'and__padded_A': ('+', 'fusion_low_padded_A', 'fusion_high_A'),
            'quotient_product': ('*', 'modulus', 'quotient_hat'),
            'congruence_right0': ('+', 'quotient_product', 'z'),
            'congruence_right': ('+', 'congruence_right0', 2),
            'projected_Ahat': ('-', 'congruence_right', 'Q'),
            'and__scaled_Z': ('*', 'joint16B', 'projected_Ahat'),
            'joint_Z_difference': ('-', 'and__scaled_Z', 'joint16B'),
        }
        assert rows['Q'] == ('+', 'modulus', 1)
    expected.update(extra)
    assert all(rows[n] == row for n, row in expected.items())
    replaced = set(expected)
    retained_outputs = {'and__bs_packed'} | ({'joint_Z_difference'} if fold_affine else set())
    erased = replaced-retained_outputs
    assert not erased & set(old['parameters']+old['auxiliaries'])
    assert not erased & leaves(old['comparisons'])
    assert not erased & leaves(old.get('interfaces', {}))
    assert not erased & leaves(old.get('public_registers', {}))
    assert not erased & leaves(old['unit_factors'])
    assert not erased & leaves(old['group_products'])
    # Every private consumer is replaced together with its producer.
    assert all(n in replaced or not erased & {a, b}
               for n, _, a, b in old['source'])
    additions = [
        ('factored_pack_q_minus_one', '-', 'and__q', 1),
        ('factored_pack_q_plus_one', '+', 'and__q', 1),
        ('factored_pack_Z', '*', 'factored_pack_q_minus_one', 'and__F3'),
        ('factored_pack_B', '+', 'and__padded_B', 'factored_pack_Z'),
        ('factored_pack_scaled_B', '*', 'factored_pack_q_plus_one', 'factored_pack_B'),
        ('factored_pack_inner', '+', 'factored_pack_A_plus_one', 'factored_pack_scaled_B'),
        ('and__bs_packed', '*', 'factored_pack_q_minus_one', 'factored_pack_inner'),
    ]
    if fold_affine:
        additions += [
            ('factored_pack_low_A_plus_one', '+', 'joint_A_sum', 13),
            ('factored_pack_A_plus_one', '+', 'factored_pack_low_A_plus_one', 'fusion_high_A'),
            ('factored_quotient_minus_one', '-', 'quotient_hat', 1),
            ('factored_unhat_product', '*', 'modulus', 'factored_quotient_minus_one'),
            ('factored_unhat', '+', 'factored_unhat_product', 'z'),
            ('joint_Z_difference', '*', 'joint16B', 'factored_unhat'),
        ]
    else:
        additions.append(('factored_pack_A_plus_one', '+', 'and__padded_A', 1))
    new_names = {n for n, _, _, _ in additions}-retained_outputs
    assert not new_names & (set(rows) | set(old['parameters']+old['auxiliaries']))
    source = [row for row in old['source'] if row[0] not in replaced]+additions
    source = SORT(source, old['parameters']+old['auxiliaries'])
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, operations=len(source),
        multiplications=counts['M'], additions_subtractions=counts['A'],
        factored_native_pack=True, folded_affine_ports=fold_affine,
        factored_pack_parent=old, factored_pack_erased_registers=sorted(erased),
        historical_computed_fields=old['computed_fields'], computed_fields=[],
        identical_complete_polynomial=True, identical_positive_coordinates=True)
    # Historical diagnostics are not advertised as live register interfaces.
    live = set(old['parameters']+old['auxiliaries']) | {n for n, _, _, _ in source}
    for key in ('fusion_interfaces', 'projected_coordinates'):
        if key in old:
            packet['historical_'+key] = old[key]
            packet[key] = {k: v for k, v in old[key].items() if leaves(v) <= live}
    if fold_affine:
        packet['projected_coordinates']['Ahat_minus_one'] = 'factored_unhat'
    assert counts['M'] == old['multiplications']
    assert counts['A'] == old['additions_subtractions']-(6 if fold_affine else 3)
    compiler.check_source(packet)
    return packet


def build(duration_parent_operations=282, *, merge_bound=True,
          parent_witnesses=None, fold_affine=True):
    return rewrite(parent.build(duration_parent_operations, merge_bound=merge_bound,
        parent_witnesses=parent_witnesses), fold_affine=fold_affine)


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound
ledger = parent.ledger


def restore_parent_registers(packet, env):
    """Diagnostic expansion of erased registers; no supplied coordinate changes."""
    q, B, Z = (env[n] for n in ('and__q', 'and__padded_B', 'and__F3'))
    A = env['factored_pack_A_plus_one']-1
    F1, F2, F0 = A-Z, B-Z, q-A-B+Z-1
    p0 = q*Z
    p1 = F2+p0
    p2 = q*p1
    p3 = F1+p2
    p4 = q*p3
    result = dict(and__F0=F0, and__F1=F1, and__F2=F2,
        computed_ports_remaining=q-A, computed_ports_before_one=q-A-F2,
        and__bs_p0=p0, and__bs_p1=p1, and__bs_p2=p2,
        and__bs_p3=p3, and__bs_p4=p4)
    assert F0+p4 == env['and__bs_packed']
    if packet['folded_affine_ports']:
        product = env['modulus']*env['quotient_hat']
        result.update(fusion_low_padded_A=env['factored_pack_low_A_plus_one']-1,
            and__padded_A=A, quotient_product=product,
            congruence_right0=product+env['z'],
            congruence_right=product+env['z']+2,
            projected_Ahat=env['factored_unhat']+1,
            and__scaled_Z=env['joint16B']*(env['factored_unhat']+1))
    assert set(result) == set(packet['factored_pack_erased_registers'])
    return result


def symbolic_audit():
    """Exact coefficient dictionaries, independent of sampled assignments."""
    zero = (0, 0, 0, 0)
    one = {zero: 1}
    def add(a, b, sign=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, 0)+sign*v
        return {k: v for k, v in out.items() if v}
    def mul(a, b):
        out = Counter()
        for k, v in a.items():
            for l, w in b.items():
                out[tuple(x+y for x, y in zip(k, l))] += v*w
        return {k: v for k, v in out.items() if v}
    q, A, B, Z = [{tuple(int(i == j) for i in range(4)): 1} for j in range(4)]
    F0 = add(add(add(add(q, A, -1), B, -1), Z), one, -1)
    left = add(F0, mul(q, add(add(A, Z, -1), mul(q, add(add(B, Z, -1), mul(q, Z))))))
    qm, qp = add(q, one, -1), add(q, one)
    right = mul(qm, add(add(one, A), mul(qp, add(B, mul(qm, Z)))))
    assert left == right and len(left) == 10
    # Reuse the four symbols as modulus,h,z,unused for the loader identity.
    old_unhat = add(add(add(mul(q, A), B), one), add(q, one), -1)
    new_unhat = add(mul(q, add(A, one, -1)), B)
    assert old_unhat == new_unhat
    return dict(exact_pack_identity_monomials=len(left), exact_loader_unhat_identity=True)


def audit(packet, seed):
    rng = random.Random(seed)
    old = packet['factored_pack_parent']
    old_source, old_output = polynomial_source(old)
    for case in range(32):
        draw = lambda: rng.randrange(1, 8) if case < 16 else rng.randrange(-5, 6)
        numerals = {n: draw() for n in compiler.NUMERALS}
        if case < 16:
            numerals.update(recoder_radix=4, repunit_divisor=7, history_radix=8)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        literal = units.constants_parent.materialize_packet(packet, numerals)
        source, output = polynomial_source(literal)
        after = execute(source, values)
        before = execute(compiler.materialize(old_source, numerals), values)
        restored = restore_parent_registers(literal, after)
        assert before[old_output] == after[output]
        assert all(before[n] == (restored[n] if n in restored else after[n])
                   for n, _, _, _ in old['source'])
        assert all(before[n] == after[n] for n in packet['unit_factors'])
        for register, group in zip(packet['group_products'], packet['factor_partition']):
            product = 1
            for index in group:
                product *= after[packet['unit_factors'][index]]
            assert product == after[register]
    return dict(whole_output_and_register_identities=32, signed_assignments=16,
        supplied_positive_assignments=16, identical_coordinate_domains=True)


def guard_audit():
    original = parent.build()
    mutations = [
        lambda p: p['source'].append(('private_consumer', '+', 'and__F0', 1)),
        lambda p: p['comparisons'].append(('and__F2', 1)),
        lambda p: p.update(public_registers={'nested': ['projected_Ahat']}),
        lambda p: p.update(interfaces={'nested': {'x': 'and__padded_A'}}),
        lambda p: p['source'].append(('factored_pack_inner', '+', 'x', 1)),
        lambda p: p.update(source=[(n, op, a, 2) if n == 'Q' else (n, op, a, b)
                                   for n, op, a, b in p['source']]),
        lambda p: p.update(source=[(n, op, a, 13) if n == 'fusion_low_padded_A' else (n, op, a, b)
                                   for n, op, a, b in p['source']]),
    ]
    for change in mutations:
        packet = copy.deepcopy(original)
        change(packet)
        try:
            rewrite(packet)
        except (AssertionError, KeyError):
            pass
        else:
            raise AssertionError('Incompatible private source accepted')
    return dict(rejected_incompatible_callers=len(mutations))


def verify():
    records = []
    for interface in (False, True):
      for folded in (False, True):
       for cost, witnesses in [(o, None) for o, _, _ in parent.parent.EXPECTED]+[(289, 46)]:
        packet = build(cost, merge_bound=interface, parent_witnesses=witnesses, fold_affine=folded)
        old = packet['factored_pack_parent']
        rec = ledger(packet)
        assert degree_bound(packet) == degree_bound(old)
        assert packet['auxiliaries'] == old['auxiliaries'] and packet['parameters'] == old['parameters']
        assert packet['comparisons'] == old['comparisons']
        assert rec['polynomial']['operations'] == len(polynomial_source(old)[0])-(6 if folded else 3)
        rec.update(folded_affine_ports=folded, duration_parent_operations=cost,
                   restricted_parent_witnesses=witnesses, audit=audit(packet, 269275+len(records)))
        source, output = polynomial_source(packet)
        parent.parent.parent.parent.source_closure(source, output)
        encoded = compiler.encode_source(source)
        rec.update(source=encoded, auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
        records.append(rec)
    default = ledger(build())
    assert default['polynomial'] == dict(operations=269, multiplications=136,
        additions_subtractions=133, degree_upper_bound=3853, exact_degree_claimed=False)
    assert default['certificate']['operations'] == 255
    assert default['certificate']['equations'] == 5 and default['certificate']['witnesses'] == 43
    selected = [r for r in records if r['folded_affine_ports'] and r['bound_is_program_E']]
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_FACTORED_PORTS269', default=default,
        mapped_cost_degree_frontier=parent.family_frontier(selected),
        fixed43_mapped_frontier=parent.family_frontier([r for r in selected if r['certificate']['witnesses'] == 43]),
        symbolic=symbolic_audit(), guards=guard_audit(), ledgers=records,
        scope='Identical complete polynomials and supplied positive zero sets; mapped selected275 family only.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(target.read_text()) == json.loads(json.dumps(result))
    print(result['status'])
    print(result['mapped_cost_degree_frontier'])
    print(result['scope'])
