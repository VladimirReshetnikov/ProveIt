#!/usr/bin/env python3
"""Pay a dyadic duration inside the existing two-core ordinary-input recoder.

The low B-bit block of the existing AND enforces n&(n-1)=0.  No third
native core is imported.  Full positive extensions are proved in the note;
finite outer fixtures deliberately do not assert full Pell zeros.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_input_dilation129 as radix4
import native_binary_input_dilation130 as inline

raw = inline.parent
geometry = raw.geometry
masked = raw.masked
execute = raw.execute
sos_source = raw.sos_source


def power_chain(width):
    assert isinstance(width, int) and width >= 2
    source = []
    exponent, register = 1, 'q'
    for bit in bin(width)[3:]:
        new_exponent = 2 * exponent
        new_register = 'Q' if new_exponent == width else f'width_power{new_exponent}'
        source.append((new_register, '*', register, register))
        exponent, register = new_exponent, new_register
        if bit == '1':
            new_exponent = exponent + 1
            new_register = 'Q' if new_exponent == width else f'width_power{new_exponent}'
            source.append((new_register, '*', register, 'q'))
            exponent, register = new_exponent, new_register
    assert exponent == width and register == 'Q'
    assert len(source) == width.bit_length() + width.bit_count() - 2
    return source


def ordinary_recoder(width):
    """Same raw relation as the existing recoders, extended to width3 too."""
    if width == 2:
        return dict(radix4.build(), width=width, power_chain_length=1)
    chain = power_chain(width)
    old = inline.build()
    assert old['source'][:3] == [('q2', '*', 'q', 'q'), ('Q', '*', 'q2', 'q2'),
                                ('B', '*', 8, 'Q')]
    source = chain + [('B', '*', 1 << (width - 1), 'Q')] + old['source'][3:]
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(old, source=source, width=width, power_chain_length=len(chain),
                operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'])


def unfused_build(width=2):
    old = ordinary_recoder(width)
    rows = {row[0]: row for row in old['source']}
    expected = {
        'and__q': ('and__q', '*', 16, 'scale'),
        'and__scaled_A': ('and__scaled_A', '*', 16, 'copies'),
        'and__scaled_B': ('and__scaled_B', '*', 16, 'K'),
        'and__scaled_Z': ('and__scaled_Z', '*', 16, 'Ahat'),
    }
    assert all(rows[name] == row for name, row in expected.items())
    # Change only these four input consumers. The original outer scale,
    # input-copy, K, Ahat and all geometry consumers remain unchanged.
    changes = {
        'and__q': ('and__q', '*', 16, 'joined_scale'),
        'and__scaled_A': ('and__scaled_A', '*', 16, 'joined_H'),
        'and__scaled_B': ('and__scaled_B', '*', 16, 'joined_M'),
        'and__scaled_Z': ('and__scaled_Z', '*', 16, 'joined_Ahat'),
    }
    extra = [
        ('duration_multiple', '*', 'Bm1', 'duration_quotient'),
        ('duration_J', '+', 'duration_multiple', 'duration'),
        ('duration_bound', '+', 'duration', 'duration_slack'),
        ('duration_minus_one', '-', 'duration', 1),
        ('shifted_H', '*', 'B', 'copies'),
        ('joined_H', '+', 'shifted_H', 'duration'),
        ('shifted_M', '*', 'B', 'K'),
        ('joined_M', '+', 'shifted_M', 'duration_minus_one'),
        ('shifted_Ahat', '*', 'B', 'Ahat'),
        ('joined_Ahat', '-', 'shifted_Ahat', 'Bm1'),
        ('joined_scale', '*', 'B', 'scale'),
    ]
    assert len(extra) == 11
    source = []
    for row in old['source']:
        if row[0] == 'and__q':
            source.extend(extra)
        source.append(changes.get(row[0], row))
    pairs = old['comparisons'] + [('duration_J', 'J'), ('duration_bound', 'Bm1')]
    auxiliaries = old['auxiliaries'] + ['duration', 'duration_quotient', 'duration_slack']
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    oldcounts = Counter('M' if op == '*' else 'A' for _, op, _, _ in old['source'])
    assert counts == oldcounts + Counter(M=5, A=6)
    assert len(pairs) == 36 and len(auxiliaries) == 52
    names = set(old['parameters'] + auxiliaries)
    for name, _, a, b in source:
        assert name not in names
        assert all(not isinstance(v, str) or v in names for v in (a, b))
        names.add(name)
    return dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
                operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'], equations=36, witnesses=52,
                changed_consumers=list(changes), new_registers=[row[0] for row in extra],
                dyadic_duration=True,
                public_registers=dict(duration='duration', power='Q', power_minus_one='modulus',
                                      output='z', base='B', joined_scale='joined_scale'))


def build(width=2):
    """Fold the joined words directly into the four existing padded ports."""
    old = unfused_build(width)
    private = {'duration_minus_one', 'shifted_H', 'joined_H', 'shifted_M', 'joined_M',
               'shifted_Ahat', 'joined_Ahat', 'joined_scale'}
    pads = {'and__q', 'and__scaled_A', 'and__padded_A', 'and__scaled_B',
            'and__padded_B', 'and__scaled_Z', 'and__F3'}
    assert len(private) == 8 and len(pads) == 7
    for name, _, a, b in old['source']:
        if a in private or b in private:
            assert name in private | pads
    assert not any(a in private or b in private for a, b in old['comparisons'])
    for scaled, consumer in [('and__scaled_A', 'and__padded_A'),
                             ('and__scaled_B', 'and__padded_B'),
                             ('and__scaled_Z', 'and__F3')]:
        assert {name for name, _, a, b in old['source'] if scaled in (a, b)} == {consumer}
        assert not any(scaled in pair for pair in old['comparisons'])
    replacement = [
        ('joint16B', '*', 16, 'B'),
        ('and__q', '*', 'joint16B', 'scale'),
        ('and__scaled_A', '*', 'joint16B', 'copies'),
        ('joint16duration', '*', 16, 'duration'),
        ('joint_A_sum', '+', 'and__scaled_A', 'joint16duration'),
        ('and__padded_A', '+', 'joint_A_sum', 12),
        ('and__scaled_B', '*', 'joint16B', 'K'),
        ('joint_B_sum', '+', 'and__scaled_B', 'joint16duration'),
        ('and__padded_B', '-', 'joint_B_sum', 6),
        ('and__scaled_Z', '*', 'joint16B', 'Ahat'),
        ('joint_Z_difference', '-', 'and__scaled_Z', 'joint16B'),
        ('and__F3', '+', 'joint_Z_difference', 8),
    ]
    source = []
    for row in old['source']:
        if row[0] == 'and__q':
            source.extend(replacement)
        if row[0] not in private | pads:
            source.append(row)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == old['operations'] - 3
    assert counts['M'] == old['multiplications'] - 2
    assert counts['A'] == old['additions_subtractions'] - 1
    ordinary = ordinary_recoder(width)
    assert len(source) == ordinary['operations'] + 8
    ordinary_rows = {row[0]: row for row in ordinary['source']}
    return dict(old, source=source, operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'], fused_paddings=True,
                deleted_join_registers=sorted(private),
                unfused_new_registers=old['new_registers'],
                new_registers=[row[0] for row in source if row[0] not in ordinary_rows],
                changed_consumers=[row[0] for row in source if row[0] in ordinary_rows
                                   and row != ordinary_rows[row[0]]],
                public_registers=dict(duration='duration', power='Q', power_minus_one='modulus',
                                      output='z', base='B', native_scale='and__q'))


def independent(packet, values):
    """Manual wrapper, existing independent geometry, separately called AND."""
    width = packet['width']
    q, P, J, K, Ahat, z = (values[name] for name in ('q', 'P', 'J', 'K', 'Ahat', 'z'))
    n = values['duration']
    Q = q ** width
    B = (1 << (width - 1)) * Q
    S, H = q * P, values['x'] * J
    answer = [(B - 1) * J + 1 - P, (2 * B - 1) * K + 1 - S,
              values['x'] + values['input_slack'] - q,
              Ahat + Q - (Q - 1) * values['quotient_hat'] - z - 2,
              z + values['output_slack'] - Q]
    geo = geometry.build(shared_B=True)
    gv = {name: values['geo__' + name] for name in geo['auxiliaries']}
    gv.update(q=q, J=J)
    answer += geometry.manual(gv, B)
    ms, mp, _ = masked.source('and64_prescribed')
    _, aux = masked.domains('and64_prescribed')
    av = {name: values['and__' + name] for name in aux}
    av.update(P=B * S, Hhat=B * H + n + 1, Mhat=B * K + n,
              Zhat=B * (Ahat - 1) + 1)
    env = masked.parent.execute(ms, av)
    answer += [env[a] - env[b] for a, b in mp]
    answer += [(B - 1) * values['duration_quotient'] + n - J,
               n + values['duration_slack'] - (B - 1)]
    return answer


def ledger(packet):
    source, out = sos_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == packet['operations'] + 107
    return dict(width=packet['width'], power_chain_length=packet['power_chain_length'],
                operations=packet['operations'], multiplications=packet['multiplications'],
                additions_subtractions=packet['additions_subtractions'], witnesses=52, equations=36,
                polynomial=dict(operations=len(source), multiplications=counts['M'],
                                additions_subtractions=counts['A'], output=out,
                                exact_degree=12 * packet['width'] + 40))


def degree_audit(packet, exact=False):
    degrees = {name: 1 for name in packet['parameters'] + packet['auxiliaries']}
    get = lambda v: degrees[v] if isinstance(v, str) else 0
    for name, op, a, b in packet['source']:
        degrees[name] = get(a) + get(b) if op == '*' else max(get(a), get(b))
    ds = [max(get(a), get(b)) for a, b in packet['comparisons']]
    expected = 6 * packet['width'] + 20
    index = packet['comparisons'].index(('and__L9', 'and__R9'))
    assert ds[index] == expected and all(d < expected for i, d in enumerate(ds) if i != index)
    answer = dict(residual_degrees=ds, unique_maximum_index=index,
                  exact_polynomial_degree=2 * expected)
    if exact:
        T = sp.Symbol('T')
        names = packet['parameters'] + packet['auxiliaries']
        weights = {name: 1 + i % 5 for i, name in enumerate(names)}
        values = {name: sp.Poly(weights[name] * T + i + 1, T) for i, name in enumerate(names)}
        env = execute(packet['source'], values)
        residuals = [env[a] - env[b] for a, b in packet['comparisons']]
        assert residuals[index].degree() == expected
        assert all(r.degree() < expected for i, r in enumerate(residuals) if i != index)
        qtop = (1 << (packet['width'] + 3)) * weights['q'] ** (packet['width'] + 1) * weights['P']
        top = weights['and__w'] ** 2 * weights['and__s'] ** 4 * weights['and__k'] ** 2 * qtop ** 6
        assert residuals[index].LC() == top
        answer['weighted_polynomial_leading_coefficient'] = str(top * top)
    return answer


def spread(x, width):
    return sum(((x >> j) & 1) << (width * j) for j in range(x.bit_length()))


def outer_fixture(x, n, width):
    assert width >= 2 and n >= 2 and 0 < x < 1 << n
    q = 1 << n
    Q = q ** width
    B = (1 << (width - 1)) * Q
    P = B ** n
    J = (P - 1) // (B - 1)
    S = q * P
    K = (S - 1) // (2 * B - 1)
    H = x * J
    A = H & K
    z = spread(x, width)
    assert J > B > q and J.bit_count() == n and J % 2 == 1
    assert A == sum(((x >> j) & 1) << (width * (n + 1) * j) for j in range(n))
    assert A >= z and (A - z) % (Q - 1) == 0 and 0 < z <= (Q - 1) // ((1 << width) - 1)
    assert divmod(J, B - 1) == ((J - n) // (B - 1), n)
    values = dict(x=x, z=z, q=q, P=P, J=J, K=K, Ahat=A + 1,
                  quotient_hat=(A - z) // (Q - 1) + 1, input_slack=q - x,
                  output_slack=Q - z, duration=n,
                  duration_quotient=(J - n) // (B - 1), duration_slack=B - 1 - n)
    assert all(v > 0 for v in values.values())
    Hj, Mj, Aj, Sj = B * H + n, B * K + n - 1, B * A, B * S
    assert 0 <= Hj < Sj and 0 <= Mj < Sj and 0 <= Aj < Sj
    assert (Hj & Mj) == B * A + (n & (n - 1))
    assert ((Hj & Mj) == Aj) == (n & (n - 1) == 0)
    if n & (n - 1) == 0:
        fields = [16 * (Sj - 1 - (Hj | Mj)) + 1,
                  16 * (Hj - Aj) + 4, 16 * (Mj - Aj) + 2, 16 * Aj + 8]
        assert all(f > 0 for f in fields)
        assert sum(fields) + 1 == 16 * Sj
        values.update({f'and__F{i}': fields[i] for i in range(3)})
    return values


def checks():
    records = []
    rng = random.Random(14052236)
    count = signed = exact_count = 0
    for width in (2, 3, 4, 5, 8, 16, 64, 160):
        packet = build(width)
        reference = unfused_build(width)
        source, out = sos_source(packet)
        for case in range(128):
            positive = case < 64
            values = {name: rng.randrange(1, 10) if positive else rng.randrange(-4, 6)
                      for name in packet['parameters'] + packet['auxiliaries']}
            env = execute(source, values)
            un = execute(reference['source'], values)
            expected = independent(packet, values)
            assert [env[a] - env[b] for a, b in packet['comparisons']] == expected
            assert [un[a] - un[b] for a, b in packet['comparisons']] == expected
            assert all(env[name] == un[name] for name in ('and__q', 'and__padded_A',
                                                         'and__padded_B', 'and__F3'))
            assert env[out] == sum(v * v for v in expected)
            if positive:
                assert un['joined_H'] + 1 > 0 and un['joined_M'] + 1 > 0
                assert un['joined_Ahat'] == env['B'] * (values['Ahat'] - 1) + 1 > 0
                assert un['joined_scale'] > 0 and env['and__F3'] >= 8
            count += 1
            signed += not positive
        exact = width in (2, 3, 4, 8, 16)
        record = ledger(packet)
        record['degree_audit'] = degree_audit(packet, exact)
        records.append(record)
        exact_count += exact
    assert records[0]['operations'] == 137
    assert (records[0]['multiplications'], records[0]['additions_subtractions']) == (68, 69)
    assert records[0]['polynomial']['operations'] == 244
    for record in records[1:]:
        assert record['operations'] == 136 + record['power_chain_length']
        assert record['multiplications'] == 68 + record['power_chain_length']
        assert record['additions_subtractions'] == 68
    outer_count = accepted = rejected = 0
    for width in (2, 3, 4, 8, 64, 160):
        packet = build(width)
        for n in range(2, 18):
            for x in (1, min(3, (1 << n) - 1), (1 << n) - 1,
                      rng.randrange(1, 1 << n)):
                values = {name: 1 for name in packet['parameters'] + packet['auxiliaries']}
                values.update(outer_fixture(x, n, width))
                env = execute(packet['source'], values)
                residuals = [env[a] - env[b] for a, b in packet['comparisons']]
                assert residuals[:5] + residuals[-2:] == [0] * 7
                if n & (n - 1) == 0:
                    for pair in [('and__bs_q', 'and__q'), ('and__input_A', 'and__padded_A'),
                                 ('and__input_B', 'and__padded_B')]:
                        assert env[pair[0]] == env[pair[1]]
                    accepted += 1
                else:
                    B = env['B']
                    assert ((B * values['x'] * values['J'] + n) &
                            (B * values['K'] + n - 1)) != B * (values['Ahat'] - 1)
                    rejected += 1
                assert residuals == independent(packet, values)
                outer_count += 1
    # Exhaustive small independent word algebra, including oversized outputs.
    word_cases = 0
    for b in range(1, 5):
        B = 1 << b
        for H in range(4):
            for M in range(4):
                for ell in range(1, B):
                    for A in range(5):
                        assert (((B * H + ell) & (B * M + ell - 1)) == B * A) == (
                            (H & M) == A and (ell & (ell - 1)) == 0)
                        word_cases += 1
    return dict(status='PASS_NATIVE_BINARY_DYADIC_DURATION_RECODER', ledgers=records,
                full_residual_and_SOS_identities=count, signed_identities=signed,
                exact_weighted_degree_audits=exact_count,
                outer_fixtures=dict(total=outer_count, dyadic=accepted, nondyadic_rejected=rejected,
                                    full_Pell_zeros_materialized=False),
                independent_exhaustive_low_block_cases=word_cases,
                width2_example=dict(build(2), polynomial=ledger(build(2))['polynomial']),
                scope='Complete positive recoding with an explicitly certified dyadic duration n>=2; '
                      'no universal tag-input composition or complete universal bound is asserted.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(checks()))
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
