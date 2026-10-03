"""Pay a fixed dilation width through the existing population geometry.

For k>=3, two gates replace the q^k chain. The raw geometry now receives
scale Q and index (2^k-1)J; its full positive converse is reconstructed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import native_binary_dyadic_duration_recoder as parent
import native_binary_dyadic_duration_units as units


def recount(packet):
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in packet['source'])
    packet.update(operations=len(packet['source']), multiplications=counts['M'],
                  additions_subtractions=counts['A'], equations=len(packet['comparisons']),
                  witnesses=len(packet['auxiliaries']))


def rewrite(old, repeated_mask):
    """Rewrite a literal raw recoder, possibly inside its complete compiler.

    repeated_mask must denote the fixed numeral 2^k-1. A caller using an
    opaque numeral must retain this exact definition in its own receipt.
    """
    k = old['width']
    assert isinstance(k, int) and k >= 3
    chain = parent.power_chain(k)
    nodes = {n: (op, a, b) for n, op, a, b in old['source']}
    assert all(nodes[n] == (op, a, b) for n, op, a, b in chain)
    private = {n for n, _, _, _ in chain} - {'Q'}
    assert all(n in private | {'Q'} for n, _, a, b in old['source']
               if a in private or b in private)
    assert not any(a in private or b in private for a, b in old['comparisons'])
    guards = {
        'geo__wn2': ('*', 'geo__w', 'q'),
        'geo__sn2': ('*', 'geo__s', 'q'),
        'geo__r1': ('+', 'J', 1),
        'geo__tr1': ('+', 'geo__r1', 'J'),
        'geo__geometry_X_bound': ('+', 'J', 'geo__bound_beta'),
        'geo__geometry_index_bound': ('+', 'B', 'geo__index_beta'),
    }
    assert all(nodes[n] == row for n, row in guards.items())
    assert {n for n, _, a, b in old['source']
            if n.startswith('geo__') and ('q' in (a, b) or 'J' in (a, b))} == set(guards)-{'geo__geometry_index_bound'}
    assert ('geo__geometry_index_bound', 'J') in old['comparisons']
    source = []
    inserted = False
    for n, op, a, b in old['source']:
        if n in private | {'Q'}:
            if not inserted:
                source += [('Q', '+', 'q', 'power_gap'),
                           ('geometry_index', '*', repeated_mask, 'J')]
                inserted = True
            continue
        if n.startswith('geo__'):
            a = {'q': 'Q', 'J': 'geometry_index'}.get(a, a)
            b = {'q': 'Q', 'J': 'geometry_index'}.get(b, b)
        source.append((n, op, a, b))
    assert inserted
    pairs = [('geo__geometry_index_bound', 'geometry_index')
             if pair == ('geo__geometry_index_bound', 'J') else pair
             for pair in old['comparisons']]
    aux = old['auxiliaries'] + ['power_gap']
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=aux,
                  power_chain_length=0, population_width=True,
                  geometry_scale='Q', geometry_input='geometry_index',
                  width_constraint_operations=2,
                  repeated_mask_definition='2^width-1')
    recount(packet)
    assert packet['operations'] == old['operations']-len(chain)+2
    assert packet['witnesses'] == old['witnesses']+1
    assert packet['equations'] == old['equations']
    return packet


def build(width=3, form='normalized'):
    assert width >= 3 and form in ('raw', 'units', 'normalized')
    packet = rewrite(parent.build(width), (1 << width)-1)
    if form != 'raw':
        packet = units.rewrite(packet, normalize_strong=form == 'normalized')
    packet['form'] = form
    return packet


def polynomial_source(packet):
    return parent.sos_source(packet) if packet['form'] == 'raw' else units.polynomial_source(packet)


def degree_bound(packet):
    """Conservative full-DAG degree propagation; no cancellation assumed."""
    degree = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    get = lambda v: degree[v] if isinstance(v, str) else 0
    source, out = polynomial_source(packet)
    for n, op, a, b in source:
        degree[n] = get(a)+get(b) if op == '*' else max(get(a), get(b))
    return degree[out]


def ledger(packet):
    source, out = polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    result = dict(width=packet['width'], form=packet['form'],
                  certificate={k: packet[k] for k in ('operations', 'multiplications',
                               'additions_subtractions', 'equations', 'witnesses')},
                  polynomial=dict(operations=len(source), multiplications=counts['M'],
                                  additions_subtractions=counts['A'], output=out),
                  degree_upper_bound=degree_bound(packet))
    expected = {'raw': (138, 36, 53, 245, 52),
                'units': (144, 17, 40, 194, 195),
                'normalized': (148, 15, 40, 192, 303)}[packet['form']]
    assert (packet['operations'], packet['equations'], packet['witnesses'],
            len(source), result['degree_upper_bound']) == expected
    return result


def independent_raw(packet, values):
    k = packet['width']
    q, P, J, K, Ahat, z = (values[n] for n in ('q', 'P', 'J', 'K', 'Ahat', 'z'))
    n = values['duration']
    Q = q+values['power_gap']
    B = (1 << (k-1))*Q
    r = ((1 << k)-1)*J
    S, H = q*P, values['x']*J
    result = [(B-1)*J+1-P, (2*B-1)*K+1-S,
              values['x']+values['input_slack']-q,
              Ahat+Q-(Q-1)*values['quotient_hat']-z-2,
              z+values['output_slack']-Q]
    geometry = parent.geometry.build(shared_B=True)
    gv = {name: values['geo__'+name] for name in geometry['auxiliaries']}
    gv.update(q=Q, J=r)
    result += parent.geometry.manual(gv, B)
    source, pairs, _ = parent.masked.source('and64_prescribed')
    _, aux = parent.masked.domains('and64_prescribed')
    av = {name: values['and__'+name] for name in aux}
    av.update(P=B*S, Hhat=B*H+n+1, Mhat=B*K+n, Zhat=B*(Ahat-1)+1)
    env = parent.masked.parent.execute(source, av)
    result += [env[a]-env[b] for a, b in pairs]
    result += [(B-1)*values['duration_quotient']+n-J,
               n+values['duration_slack']-(B-1)]
    return result


def outer_fixture(k, n, x):
    assert k >= 3 and n >= 2 and 0 < x < 1 << n
    q = 1 << n
    Q = 1 << (k*n)
    B = (1 << (k-1))*Q
    P = B**n
    J = (P-1)//(B-1)
    K = (q*P-1)//(2*B-1)
    r = ((1 << k)-1)*J
    assert r > B >= 12 and r > Q and r & 1
    assert r.bit_count() == k*n and Q == 1 << r.bit_count()
    assert Q-q > 0 and n < B-1
    H = x*J
    A = H & K
    z = sum(((x >> j) & 1) << (k*j) for j in range(n))
    assert A == sum(((x >> j) & 1) << (k*(n+1)*j) for j in range(n))
    assert A % (Q-1) == z and 0 < z < Q-1
    v, rem = divmod(J-n, B-1)
    assert not rem and v > 0
    values = dict(x=x, z=z, q=q, P=P, J=J, K=K, Ahat=A+1,
                  quotient_hat=(A-z)//(Q-1)+1, input_slack=q-x,
                  output_slack=Q-z, duration=n, duration_quotient=v,
                  duration_slack=B-1-n, power_gap=Q-q)
    assert all(v > 0 for v in values.values())
    joined = (B*H+n) & (B*K+n-1)
    assert joined == B*A+(n & (n-1))
    assert (joined == B*A) == (n & (n-1) == 0)
    assert max(B*H+n, B*K+n-1, B*A) < B*q*P
    return values


def verify():
    rng = random.Random(19240303)
    records = []
    raw_cases = unit_cases = signed = outer = dyadic = 0
    for k in (3, 4, 8, 16, 64, 160):
        p = build(k, 'raw')
        for case in range(64):
            values = {n: rng.randrange(1, 7) if case < 32 else rng.randrange(-3, 5)
                      for n in p['parameters']+p['auxiliaries']}
            env = parent.execute(p['source'], values)
            residuals = [env[a]-env[b] for a, b in p['comparisons']]
            expected = independent_raw(p, values)
            assert residuals == expected
            source, out = polynomial_source(p)
            assert parent.execute(source, values)[out] == sum(x*x for x in expected)
            raw_cases += 1
            signed += case >= 32
        for form in ('raw', 'units', 'normalized'):
            packet = build(k, form)
            records.append(ledger(packet))
            if form != 'raw' and k <= 16:
                for case in range(32):
                    values = {n: rng.randrange(1, 5) if case < 16 else rng.randrange(-2, 4)
                              for n in packet['parameters']+packet['auxiliaries']}
                    units.audit_identity(packet, values)
                    unit_cases += 1
                    signed += case >= 16
        for n in range(2, 11):
            for x in {1, (1 << n)-1, 1 << (n-1), rng.randrange(1, 1 << n)}:
                outer_fixture(k, n, x)
                outer += 1
                dyadic += n & (n-1) == 0
    # Exhaust bounded binary exponents independently of the actual outer
    # fixture builder. Only the desired common repunit duration survives.
    synchronizations = accepted = 0
    for k in range(3, 9):
        for b in range(k, 65):
            B, Q = 1 << b, 1 << (b-k+1)
            for n in range(1, 9):
                P = B**n
                J = (P-1)//(B-1)
                r = ((1 << k)-1)*J
                assert r.bit_count() == k*n
                if not (r > B and Q == 1 << r.bit_count()):
                    continue
                for m in range(1, n+4):
                    e = (b+1)*m-b*n
                    admissible = 0 < e < b-k+1  # q<Q, exactly the gap domain.
                    assert admissible == (m == n)
                    synchronizations += 1
                    accepted += admissible
    packet = build(3)
    source, out = polynomial_source(packet)
    encoded = [list(row) for row in source]
    return dict(status='PASS_NATIVE_BINARY_POPULATION_WIDTH_RECODER', ledgers=records,
                checks=dict(independent_raw_residual_and_SOS_cases=raw_cases,
                            full_unit_correction_and_output_cases=unit_cases,
                            signed_cases=signed, genuine_outer_cases=outer,
                            dyadic_outer_cases=dyadic, nondyadic_outer_cases=outer-dyadic,
                            repunit_synchronization_candidates=synchronizations,
                            synchronized_cases=accepted),
                example=dict(parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             source=encoded, comparisons=packet['comparisons'], output=out,
                             source_sha256=hashlib.sha256(json.dumps(encoded).encode()).hexdigest()),
                scope='For every fixed width k>=3, the complete positive dyadic-duration '
                      'spread relation costs192 polynomial operations with40 positive witnesses. '
                      'All width dependence is in two fixed numerals, each use paid. '
                      'Degree upper bounds only; full canonical native auxiliaries are proved '
                      'parametrically, not materialized. No universal tag composition here.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
