"""An infinite family of complete positive zeros of the unchanged86 candidate.

The scalar compiler constants are explicit.  No universal program is
instantiated and no false-input claim is made.  Huge witnesses are specified
by exact Pell recipes and an irrational-rotation existence proof, not printed.
"""
import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path
import random
import sympy as sp

import complete75_weakened86_infinite_outer_family as outer
import complete75_weakened86_auxiliary_sign_lift as auxiliary

candidate = auxiliary.candidate
pell, pell_mod = auxiliary.pell, auxiliary.pell_mod
P0 = 1316212416417369613
P_STEP = 2514909272844107199283200
N_RESIDUE = 13587
N_MODULUS = 16777216
WRAP = 46
CONCRETE_P = 3572130746085641437869936970845936422413
CONCRETE_N = 2381436634762533967520279822849047278867


def seed():
    d = outer.family_data(4)
    A, a, H, E = (d[n] for n in ('A', 'a', 'H', 'E'))
    M, MC, MF, inner, epsilon, lam, omega = 255, 6, 12, 1, -1, 1, -1
    K = 16*14*M+MC+16*(MF+15)
    v = 8+inner
    chi_v, psi_v = pell(A, v)
    Fv = chi_v+a*psi_v
    Delta = A*A-1
    delta = (psi_v-v)//Delta
    assert delta > 0 and psi_v == v+Delta*delta
    TH, TM, L = 8758492, 24, 6306114240
    modulus = M*H
    assert pow(2, TH, H) == 1
    assert pell_mod(A, TM, M) == (1, 0)
    assert L == 5*6*TH*TM
    assert pell_mod(A, L, modulus) == (1, 0)
    assert L % (2*TH) == L % 4 == 0
    c13 = pell_mod(A, 13, modulus)[1]
    rhs = M*Fv-K-epsilon+lam-13-WRAP*c13
    divisor = gcd(L, modulus)
    assert divisor == 45 and rhs % divisor == 0
    z0 = (rhs//divisor)*pow(L//divisor, -1, modulus//divisor) % (modulus//divisor)
    p0 = 13+L*z0
    initial_step = L*(modulus//divisor)
    assert pell_mod(A, E, E) == (1, 0)
    step = lcm(initial_step, E)
    assert p0 == P0 and step == P_STEP
    cE = pell_mod(A, p0, E)[1]
    numerator = lam-p0-WRAP*cE
    assert numerator % 2 == 0
    n0 = (numerator//2) % (E//2)
    assert n0 == N_RESIDUE and E//2 == N_MODULUS
    assert 0 < WRAP < M-1
    # These small, exact base inequalities imply all positive p>=13 tails.
    cp, prev = pell(A, 13)[1], pell(A, 12)[1]
    assert cp > M*Fv+K+13
    assert cp-prev > d['X']
    assert d['P'] % E == 1
    return dict(**d, MC=MC, MF=MF, inner_bits=inner, epsilon=epsilon,
        lam=lam, omega=omega, wrap=WRAP, M=M, K=K, input_index=v,
        input_chi=chi_v, input_psi=psi_v, Fv=Fv, positive_delta=delta,
        main_return_period=TH, mask_return_period=TM,
        combined_Pell_return=L, combined_modulus=modulus, linear_gcd=divisor,
        c13_mod_combined=c13, linear_progression_index=z0,
        p0=p0, initial_p_step=initial_step, p_step=step,
        c_mod_E=cE, n_residue=n0, n_modulus=E//2,
        small_positivity_base_index=13,
        scope='Exact full-zero existence for explicit scalar compiler constants; '
              'no universal program or false input is identified.')


def progression_audit(d):
    A, H, M, E = (d[n] for n in ('A', 'H', 'M', 'E'))
    rng = random.Random(8601901)
    visits = [0, 1, 2, 17, 1000]+[rng.randrange(0, 10**35) for _ in range(123)]
    for index in visits:
        p = d['p0']+d['p_step']*index
        cMH = pell_mod(A, p, M*H)[1]
        cE = pell_mod(A, p, E)[1]
        assert p % 4 == 1 and p > 13
        assert pow(2, p, H) == d['X']
        assert (d['K']-2+p+WRAP*cMH-M*d['Fv']) % (M*H) == 0
        assert cE == d['c_mod_E']
        assert (2*d['n_residue']+p+WRAP*cE-1) % E == 0
    # Integer upper/lower positivity proof checked on fully materialized tails.
    small = []
    for p in range(13, 78, 2):
        chi, c = pell(A, p)
        N = d['K']-2+p+WRAP*c-M*d['Fv']
        gammaH = chi-d['a']*c-d['X']
        assert 0 < N < (WRAP+1)*c < M*c < M*gammaH
        assert d['K']-(N+M*d['Fv']) == -p-WRAP*c+2 < 0
        small.append(p)
    # P=1 modulo E, so psi_P(n)=n modulo E for every n.
    for _ in range(128):
        n = d['n_residue']+d['n_modulus']*rng.randrange(0, 10**30)
        assert pell_mod(d['P'], n, E)[1] == n % E
    return dict(exact_progression_visits=len(visits), small_positive_tail_cases=len(small),
        exact_first_index_congruence_visits=128,
        warning='The small p tails are inequalities, not claimed ratio or integral-rho fixtures.')


def concrete_certificate(d, bits):
    """Exact finite certificates for the fully specified giant-index recipe."""
    p, n = CONCRETE_P, CONCRETE_N
    assert (p-d['p0']) % d['p_step'] == 0
    assert (p-d['p0'])//d['p_step'] == 1420381555969979
    assert n % d['n_modulus'] == d['n_residue']
    assert n < p < 2*n and p % 4 == 1
    assert pow(2, p, d['H']) == d['X']
    cMH = pell_mod(d['A'], p, d['M']*d['H'])[1]
    assert (d['K']-2+p+WRAP*cMH-d['M']*d['Fv']) % (d['M']*d['H']) == 0
    cE = pell_mod(d['A'], p, d['E'])[1]
    kE = 2*pell_mod(d['P'], n, d['E'])[1] % d['E']
    assert (kE+p+WRAP*cE-1) % d['E'] == 0
    arithmetic = outer.IntegerIntervals(bits)
    c = arithmetic.pell(d['A'], p)[1]
    k = arithmetic.mul(arithmetic.exact(2), arithmetic.pell(d['P'], n)[1])
    low = arithmetic.mul(k, arithmetic.exact(d['Y']))
    high = arithmetic.mul(k, arithmetic.exact(d['Y']+1))
    assert arithmetic.compare(c[0], low[1]) > 0
    assert arithmetic.compare(c[1], high[0]) < 0
    bit_length = c[0][0].bit_length()+c[0][1]
    assert bit_length == c[1][0].bit_length()+c[1][1]
    return dict(precision_bits=bits, p=p, n=n, odd_gap=2*n-p,
        progression_index=1420381555969979, main_psi_interval=c,
        first_kY_interval=low, first_kY_plus_k_interval=high,
        exact_c_bit_length=bit_length, c_mod_E=cE, k_mod_E=kE,
        both_strict_ratios_certified=True,
        scope='Exact integer certificates for the full19-coordinate Pell recipe. '
              'The enormous coordinate integers and full polynomial evaluation are not materialized.')


def exact_divide(numerator, denominator):
    """Preserve exactness for Python integers, rational and symbolic inputs."""
    if isinstance(numerator, sp.Basic) or isinstance(denominator, sp.Basic):
        return numerator/denominator
    return Fraction(numerator)/Fraction(denominator)


def mapped_values(d, p, c, k, chi_first, chi_main, f, i, V, y, DC=3, DR=5):
    """Formal full-source substitution; rational off-zero values are allowed."""
    Y, X, H, E, M = (d[n] for n in ('Y', 'X', 'H', 'E', 'M'))
    N = d['K']-2+p+WRAP*c-M*d['Fv']
    rho = exact_divide(N, M*H)
    gamma = exact_divide(chi_main-d['a']*c-X, H)
    target = -p-WRAP*c
    values = dict(Jrep=1, F=2, alpha=6, zplus=1, f=f,
        h=exact_divide(k+p+WRAP*c-1, E), i=i,
        j=exact_divide(V+target, c), o=exact_divide(V+c, f),
        s=1, w=2, tau_gap=chi_first-X*Y*Y*k,
        eta=c-k*Y, zeta=k*(Y+1)-c, y_aux=y,
        Z=rho*H+d['Fv'], delta=d['positive_delta'], rho=rho, sigma=gamma-rho,
        x=1, B=16, DC=DC, DR=DR, MC=6, MF=12, cell_bits=4, inner_bits=1)
    return values


def source_audit(d):
    p, c, k, U, W, f, i, V, y, DC, DR = sp.symbols('p c k U W f i V y DC DR', nonzero=True)
    values = mapped_values(d, p, c, k, U, W, f, i, V, y, DC, DR)
    env = candidate.eliminated.run(candidate.sources()[3], candidate.eliminated.fixed_inputs(values))
    Delta, L = d['Delta_A'], d['X']*d['Y']**2
    expected = dict(norm_first=U*U-L*(L+1)*k*k,
        norm_main=W*W-Delta*c*c, norm_input=sp.Integer(1),
        norm_aux=Delta**2*i*i*c**4*(V*V-y*y)+y*y,
        norm_index=sp.Integer(-1), norm_transport=sp.Integer(-1),
        norm_strong=f*f-Delta*i*i*c**4, norm_linear=sp.Integer(1))
    assert set(expected) == set(candidate.FACTOR_NAMES)
    for name, expression in expected.items():
        assert sp.cancel(env[name]-expression) == 0, name
    assert sp.cancel(env['r_lhs']-(-p-WRAP*c+2)) == 0
    assert sp.cancel(env['exponent_rhs']+d['input_chi']) == 0
    assert sp.cancel(env['index_rhs']-d['input_psi']) == 0
    product = sp.prod(expected[n] for n in candidate.FACTOR_NAMES)-1
    assert sp.cancel(env['polynomial']-product) == 0
    rng = random.Random(861919)
    cases = 0
    for signed in (False, True):
        for _ in range(96):
            vals = [Fraction(rng.randrange(1, 10)*(-1 if signed and rng.randrange(2) else 1))
                    for _ in range(9)]
            pp, cc, kk, uu, ww, ff, ii, vv, yy = vals
            DCv, DRv = rng.randrange(1, 100), rng.randrange(1, 100)
            integer_map = mapped_values(d, *(int(v) for v in vals), DCv, DRv)
            rational_map = mapped_values(d, *vals, DCv, DRv)
            assert integer_map == rational_map
            assert not any(isinstance(v, float) for v in integer_map.values())
            actual = candidate.eliminated.run(candidate.sources()[3],
                candidate.eliminated.fixed_inputs(mapped_values(d, *vals, DCv, DRv)))
            scalar = dict(norm_first=uu*uu-L*(L+1)*kk*kk,
                norm_main=ww*ww-Delta*cc*cc, norm_input=1,
                norm_aux=Delta**2*ii*ii*cc**4*(vv*vv-yy*yy)+yy*yy,
                norm_index=-1, norm_transport=-1,
                norm_strong=ff*ff-Delta*ii*ii*cc**4, norm_linear=1)
            final = Fraction(1)
            for name in candidate.FACTOR_NAMES:
                assert actual[name] == scalar[name]
                final *= scalar[name]
            assert actual['polynomial'] == final-1
            cases += 1
    return dict(source=auxiliary.residues.inherited.source_contract(),
        all_eight_symbolic_factor_identities=True, symbolic_complete_output_identity=True,
        integer_root_and_index_identities=True, numerical_rational_output_checks=cases,
        signed_cases=cases//2, integer_and_rational_mapping_checks=cases,
        exact_zero_factor_values=[1, 1, 1, 1, -1, -1, 1, 1],
        source_scope='All86 literal operations are executed unchanged. Rational arbitrary-point '
                     'audits verify identities; positivity and integer full zeros follow from the theorem.')


def verify():
    d = seed()
    concrete = [concrete_certificate(d, bits) for bits in (256, 384)]
    for key in ('main_psi_interval', 'first_kY_interval', 'first_kY_plus_k_interval'):
        assert outer.IntegerIntervals.compare(concrete[1][key][0], concrete[0][key][0]) >= 0
        assert outer.IntegerIntervals.compare(concrete[1][key][1], concrete[0][key][1]) <= 0
    return dict(status='PASS_COMPLETE_NEGATIVE_FAMILY_FOR_SCALAR_86', seed=d,
        progressions=progression_audit(d), literal_source=source_audit(d),
        concrete_full_zero_recipe_certificates=concrete,
        witness_recipe=dict(p='p0+p_step*t',
            n='n_residue modulo n_modulus; choose an irrational-rotation ratio hit',
            c='psi_A(p)', k='2*psi_P(n)',
            rho='(K-2+p+46*c-M*Fv)/(M*H)',
            gamma='(chi_A(p)-a*c-X)/H', sigma='gamma-rho',
            Z='rho*H+Fv', delta='(psi_A(9)-9)/(A^2-1)',
            h='(k+p+46*c-1)/E', R='-p-46*c+2', mu='-chi_A(9)',
            auxiliary='p=1 modulo4, target=-p-46*c: m=2*c*p; '
                      'ell=p+2*m; V>47*c>p+46*c makes all auxiliary coordinates positive',
            other_coordinates='Jrep=1,F=2,alpha=6,zplus=1,s=1,w=2; '
                              'eta=c-kY,zeta=k(Y+1)-c,tau_gap=chi_P(n)-XY^2*k'),
        theorem='For B16,cell_bits4,inner_bits1,MC6,MF12 and arbitrary positive DC,DR, '
                'the unchanged86 polynomial has infinitely many complete positive19-coordinate '
                'zeros at x1 with R<0,mu<0 and unbounded odd gaps.',
        scope='The proof specifies exact witnesses by Pell recipes and an irrational-rotation '
              'existence argument; no astronomical full tuple is materialized. No actual universal '
              'program, false input, below87 universal bound or change to the75/87 results is asserted.')


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
    print(result['theorem'])
    print(result['scope'])
