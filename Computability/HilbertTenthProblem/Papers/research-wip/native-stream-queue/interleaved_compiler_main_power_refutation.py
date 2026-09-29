#!/usr/bin/env python3
"""Refute the 74-operation interleaving source even with doubled main X."""
from collections import Counter
from pathlib import Path
import argparse
import json
import sympy as sp
import interleaved_compiler_collapse_refutation as prior

half = prior.half
BASE = prior.BASE
NAMES = [name for name in prior.NAMES+['Z', 'F'] if name not in ('P', 'v')]
OUTER = [
    ('bounded', '+', 'C', 'alpha'),
    ('twiceX', '*', 2, 'wn2'),
    ('marked_rhs', '+', 'Z', 'W'),
    ('BF', '*', 'B', 'F'),
    ('V_rhs', '+', 'Z', 'BF'),
    ('K', '+', 'Kconstant', 'twiceX'),
    ('KC', '*', 'K', 'C'),
    ('zqm1', '*', 'zquot', 'qm1'),
    ('transport_rhs', '+', 'F', 'zqm1'),
]
SCHEDULE = prior.OUTER + half.CORE + OUTER + BASE.ADAPTER
EQUALITIES = list(half.EQUALITIES) + [
    ('C', 'marked_rhs'), ('V', 'V_rhs'), ('KC', 'transport_rhs'), ('raw_bound', 'q')
] + BASE.EQUALITIES[15:]


def source_audit():
    z = {name: sp.Symbol(name, positive=True, integer=True)
         for name in NAMES+prior.CONSTANTS+['x']}
    env = half.run(SCHEDULE, dict(z, Bm1=z['Q']-1,
                    Kconstant=z['DC']+z['Q']*z['DR'], twice_cell_bits=4*z['cell_bits']))
    sources = list(half.sources(dict(z, B=z['Q'], F=z['V'])))
    q, X, a = z['n']**2, z['w']*z['n']**3, z['a']
    D, H = (a+2)**2-1, 4*a+3
    u = 4*z['cell_bits']*z['x']+z['inner_bits']
    sources += [
        z['C']-z['Z']-z['W'],
        z['V']-z['Z']-z['B']*z['F'],
        (z['DC']+z['Q']*z['DR']+2*X)*z['C']-z['F']-z['zquot']*(q-1),
        z['C']+z['alpha']+4*z['cell_bits']*z['x']-q,
        z['kappa']-u-z['delta']*D,
        z['c']-z['kappa']-z['phi'],
        z['mu']**2-1-D*z['kappa']**2,
        z['mu']-z['W']-a*z['kappa']-z['rho']*H,
    ]
    U = z['j']*z['c']-(2*z['r']+1)
    correction = sources[9]*(U**2-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if ix == 10 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(index=ix, equality=[left, right], source_sign=sign))
    counts = Counter('M' if row[1] == '*' else 'A' for row in SCHEDULE)
    assert len(SCHEDULE) == 74 and counts == {'M': 41, 'A': 33}
    assert len(NAMES) == len(set(NAMES)) == 31
    assert len(EQUALITIES) == len(sources) == 20
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    # Exact transport lift, with a fresh positive existential quotient.
    P0, lam, C, F, K0, qq = sp.symbols('P0 lam C F K0 qq')
    assert sp.expand((K0+P0+lam*(qq-1))*C-F-(1+lam*C)*(qq-1)
                     -((K0+P0)*C-F-(qq-1))) == 0
    return dict(operations=74, multiplications=41, additions_subtractions=33,
                positive_coordinates=31, equations=20,
                schedule=[list(row) for row in SCHEDULE], source_checks=records,
                temporal_multiplier='twiceX=2*w*n^3, with X=2^(2r+1)',
                input_exponent='4*cell_bits*x+inner_bits',
                exact_transport_lift=True)


def finite_outer_examples():
    import explore_pell_kernel_prime_padding as control
    # Small illustrative half mask. d=1 is not an actual native compiler
    # width; the large n and exact population meet the old positive converse.
    B, d, b, Q, m, DC, DR, h = 2, 1, 1, 4, 2, 1, 1, 1
    K0, P0 = DC+Q*DR, Q**h
    K, L = K0+P0, 1+B*(K0+P0)
    S, ell, k, exponent = L*d, 37, 18, 3
    orbit = control.prepare_orbit(Q, S, ell, k, exponent, shift=2)
    N = ell**exponent
    n, q = B**N, Q**N
    J, Dperiod = (q-1)//(Q-1), d*N
    M, fixed = m*J, 1+Q**(N-1)
    assert sp.isprime(ell) and ell % 2 and (Q**k-1) % (ell*S) == 0
    assert sp.gcd(q-1, Dperiod) == sp.gcd(L, Dperiod) == 1
    records = []
    for x in (1, 2, 3):
        u, scaled = 4*d*x+b, 4*d*x
        W = 1 << u
        transport_residue = (-W-B*(q-1)) % L
        exponent_residue = (q+(M+1-d*h)*pow(q-1, -1, Dperiod)) % Dperiod
        # CRT for the actual affine packed index and fixed-stride transport.
        target = (transport_residue+L*((exponent_residue-transport_residue)
                  *pow(L, -1, Dperiod) % Dperiod)) % (L*Dperiod)
        selected = control.select_subset(orbit, (target-fixed) % (L*Dperiod))
        positions = selected['positions']
        assert len(positions) == len(set(positions))
        assert all(0 < position < N-1 for position in positions)
        V = fixed+sum(Q**position for position in positions)
        assert V % (L*Dperiod) == target
        C, rem = divmod(V+W+B*(q-1), L)
        Z = C-W
        F, frem = divmod(V+W-C, B)
        alpha = q-C-scaled
        r = (q-V)*(q-1)+M
        assert rem == frem == 0 and min(C, Z, F, alpha) > 0
        assert C == Z+W and V == Z+B*F and K*C == F+q-1
        assert 0 < F < q//B and W < C < q and C+alpha+scaled == q
        assert 0 < V < q and V & M == 0 and V % 2 == r % 2 == 1
        assert q <= r < q*q and r.bit_count() == 3*d*N
        assert n**3 < r*r and u < q < 2*r+1
        assert (r+1-d*h) % Dperiod == 0
        # This is the exact exponent reduction proving 2X == P0 mod(q-1).
        assert (2*r+2) % (2*d*N) == (2*d*h) % (2*d*N)
        assert r+1 > d*h
        records.append(dict(x=x, B=B, m=m, N=N, ell=ell, k=k, L=L,
                            selected_cells=len(positions), maximum_cell=max(positions),
                            q_bits=q.bit_length(), packed_index_bits=r.bit_length(),
                            packed_population=r.bit_count(), all_outer_coordinates_positive=True,
                            actual_packed_exponent_congruence=True,
                            doubled_main_power_materialized=False))
    return dict(examples=records, scope='Exact outer tuples at their actual packed indices; '
                'Pell and huge transported quotient supplied parametrically.')


def verify():
    return dict(status='PASS_FULL_DOUBLED_MAIN_POWER_INTERLEAVE74_REFUTATION',
                source=source_audit(), outer=finite_outer_examples(),
                established_complete_bound=76,
                scope='New interleaving74 source with actual reused main Pell power is false; '
                      'earlier open75 candidates remain open.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print(result['source']['operations'], result['source']['positive_coordinates'],
          result['source']['equations'])
    print(result['outer'])
