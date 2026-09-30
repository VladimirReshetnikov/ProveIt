"""Exact contextual codes and a width-dependent phase cycle; no compiler."""
import argparse
from itertools import product
import json
from pathlib import Path
import sympy as sp


def word(bits):
    return sum(bit*3**j for j, bit in enumerate(bits))


def filter_pair(read, append):
    return all(d0+a0+a1 == 1 for (d0, d1), (a0, a1) in zip(read, append))


def codes(ell):
    # Every recurrent physical word is exactly one disjoint edge (u,v).
    answer = []
    for letters in product(((0, 0), (1, 0), (0, 1)), repeat=ell):
        u = tuple(1-p-s for p, s in letters)
        v = tuple(p for p, s in letters)
        assert all(ui+vi <= 1 for ui, vi in zip(u, v))
        assert tuple((vi, 1-ui-vi) for ui, vi in zip(u, v)) == letters
        answer.append((u, v, letters))
    return answer


def edge_code_checks():
    rows = []
    for ell in range(1, 5):
        vertices = codes(ell)
        pairs = admitted = distinct_binary = 0
        for u, v, read in vertices:
            for up, vp, append in vertices:
                actual = filter_pair(read, append)
                assert actual == (up == v)
                pairs += 1; admitted += actual
                if read != append:
                    # The three logical edges 00,01,10 already force collapse.
                    assert not (filter_pair(read, read) and filter_pair(read, append)
                                and filter_pair(append, read))
                    distinct_binary += 1
        assert len(vertices) == 3**ell and pairs == 9**ell and admitted == 5**ell
        rows.append(dict(block_length=ell, edge_codes=len(vertices), physical_code_pairs=pairs,
                         allowed_overlap_pairs=admitted, distinct_two_code_pairs=distinct_binary))
    Z = ((0, 0),); P = ((1, 0),); S = ((0, 1),)
    initial = (Z, S); temporary = (P, S)
    assert all(filter_pair(read, append) for read in initial for append in temporary)
    assert all(filter_pair(temporary[i], initial[i]) for i in (0, 1))
    return dict(domains=rows, total_code_pairs=sum(row['physical_code_pairs'] for row in rows),
                total_allowed=sum(row['allowed_overlap_pairs'] for row in rows),
                two_phase_interface=dict(initial=['00', '01'], temporary=['10', '01'],
                                         all_four_computation_pairs_allowed=True,
                                         identity_return_pairs_allowed=True))


def exact_algebra():
    g0, g1, g2, B, H, U, V, Vnext = sp.symbols('g0 g1 g2 B H U V Vnext')
    raw = g0*Vnext+g1*(H-V-Vnext)+g2*(H-U-V)
    expected = (g1+g2)*H-g2*U-(g1+g2)*V+(g0-g1)*Vnext
    assert sp.expand(raw-expected) == 0
    W, N0, N1, k, a0, a1, d0, d1 = sp.symbols('W N0 N1 k a0 a1 d0 d1')
    T = g1+g2*W; F = g0-(W+1)*T
    Z = k-T*N0+g2*N1
    N0next = (N0-d0+W*a0)/3
    N1next = (N1-d1+W*a1)/3
    knext = (k+g0*a0+g1*a1+g2*d1)/3
    Znext = knext-T*N0next+g2*N1next
    assert sp.expand((3*Znext-Z-T-F*a0).subs(d0, 1-a0-a1)) == 0
    assert sp.expand((3*(2*Znext-T)-(2*Z-T)-2*F*a0).subs(d0, 1-a0-a1)) == 0
    I0, I1, A0, A1, q, cs = sp.symbols('I0 I1 A0 A1 q cs')
    carry = g0*A0+g1*A1+g2*(I1+W*A1)+cs
    eliminated = carry.subs(A1, (q-1)/2-I0-(W+1)*A0)
    expected_eliminated = F*A0+T*((q-1)/2-I0)+g2*I1+cs
    assert sp.expand(eliminated-expected_eliminated) == 0
    return dict(macro_increment=str(sp.expand(expected)),
                scalar_projection=dict(T=str(T), F=str(F), Z=str(Z),
                                       equation='3*Z_next=Z+T+F*a0',
                                       centered='V=2*Z-T; 3*V_next=V+2*F*a0'),
                empty_endpoint_identity=str(sp.expand(expected_eliminated)))


PHYSICAL = {'Z': (0, 0), 'P': (1, 0), 'S': (0, 1), 'B': (1, 1)}


def transitions(carry, read):
    d0, d1 = PHYSICAL[read]
    result = []
    for append, (a0, a1) in PHYSICAL.items():
        if a0+a1+d0 != 1:
            continue
        numerator = carry+2*a0+3*a1-3*d1
        if numerator % 3 == 0:
            result.append((numerator//3, append))
    return result


def phase_cycles():
    expected = {
        (0, 'Z'): [(1, 'S')], (0, 'P'): [(0, 'Z')],
        (0, 'S'): [(0, 'S')], (0, 'B'): [(-1, 'Z')],
        (1, 'Z'): [(1, 'P')], (1, 'P'): [],
        (1, 'S'): [(0, 'P')], (1, 'B'): []}
    for key, value in expected.items():
        assert transitions(*key) == value
    assert all(transitions(-1, symbol) == [] for symbol in PHYSICAL)
    examples = []
    for m in range(1, 101):
        carry = 0; queue = ['Z']*m; visited = set(); states = []
        for time in range(2*m+1):
            key = (carry, tuple(queue))
            assert key not in visited
            visited.add(key); states.append(key)
            options = transitions(carry, queue.pop(0))
            assert len(options) == 1
            carry, append = options[0]; queue.append(append)
        assert carry == 0 and queue == ['Z']*m
        for i in range(1, m+1):
            assert states[i] == (1, tuple(['Z']*(m-i)+['S']+['P']*(i-1)))
        for j in range(m):
            assert states[m+1+j] == (0, tuple(['P']*(m-j)+['Z']*j))
        if m in (1, 2, 5, 20, 100):
            examples.append(dict(width=m, exact_period=2*m+1))
    return dict(centered_weights=[2, 3, -3], initial_and_final_carry=0,
                reachable_carries=[-1, 0, 1], dead_carry=-1,
                tested_widths=100, period_examples=examples,
                scope='Exact physical phase cycle from an empty queue; it is not an ordinary-positive-input accepted witness')


def verify():
    return dict(status='PASS_PAIRED_CONTEXTUAL_CODE_INTERFACES',
                codes=edge_code_checks(), algebra=exact_algebra(), cycles=phase_cycles(),
                scope='Exact design interfaces only; selected block alphabet, loading, synchronization and universal acceptance remain unpaid',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = verify(); path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(json.dumps(result, indent=2))
