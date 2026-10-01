"""Finite audits for the parametric all-input collapse of the86 candidate.

Existence uses the accompanying Dirichlet/irrational-rotation proof.
The small prime host is a modular fixture, not a full candidate zero.
"""
import argparse
from fractions import Fraction
import json
from math import gcd, lcm, prod
from pathlib import Path
import random

import sympy as sp
import complete75_weakened86_auxiliary_sign_lift as auxiliary
from complete75_weakened86_full_negative_family import exact_divide

candidate = auxiliary.candidate
pell, pell_mod = auxiliary.pell, auxiliary.pell_mod


def theorem_contract():
    return dict(source=auxiliary.residues.inherited.source_contract(),
        hypotheses='B=2^d; d positive odd, 3 does not divide d; b positive odd; '
                   'MC positive even; MF,DC,DR positive; x positive.',
        conclusion='Every positive x has infinitely many complete positive19-coordinate '
                   'zeros of the unchanged86 polynomial, with R<0 and negative input root.',
        existence_dependencies=['Dirichlet primes in a coprime arithmetic progression',
                                'irrational rotation', 'proved positive auxiliary Pell lift'],
        established_75_87_unchanged=True,
        witness_materialization_claimed=False)


def wrap_choices(M, K):
    assert M >= 3 and M % 2 and K % 2 == 0
    result = []
    for epsilon in (-1, 1):
        for t in (1, -1):
            for omega in (1, -1):
                for sigma in (1, -1):
                    rhs = omega+t*(M*sigma-K-2*epsilon)
                    assert rhs % 2 == 0
                    j = rhs % (6*M)
                    if 0 < j < 2*M:
                        result.append(dict(epsilon=epsilon, t=t, omega=omega,
                                           input_sign=sigma, wrap=j))
    assert result
    return result


def wrap_audit():
    cases = boundaries = 0
    for M in range(3, 130, 2):
        for K in range(0, 6*M, 2):
            choices = wrap_choices(M, K)
            for v in choices:
                assert v['wrap'] % 2 == 0 and 2 <= v['wrap'] <= 2*M-2
                assert (v['wrap']-v['omega']-v['t']*(M*v['input_sign']-K-2*v['epsilon'])) % (3*M) == 0
            if (M-K+3) % (2*M) == 0:
                boundaries += 1
                assert any(v['epsilon'] == 1 for v in choices)
            cases += 1
    return dict(exhaustive_even_K_residue_cases=cases, boundary_cases=boundaries,
                odd_M_range=[3, 129], scope='Finite corroboration of the interval-covering proof.')


def choose_exponent(D, M, t):
    assert D % 2 and D % 3 and t in (-1, 1)
    step = lcm(18*M, D)
    e = t+step*((3*D-t+step-1)//step)
    if e % 4 != 3:
        e += step
    assert e >= 3*D and e % 4 == 3 and (e-t) % (18*M) == (e-t) % D == 0
    return e


def width_audit():
    records = []
    for D in (1, 5, 7, 11, 13, 17, 19, 25, 35, 125):
        q = 1 << D
        M, m = q*q-1, (q*q-1)//3
        assert M % 9 in (3, 6)
        for t in (1, -1):
            e = choose_exponent(D, M, t)
            assert gcd(pow(2, e, M)+1, M) == 3
            assert (pow(2, e, 9)+1) % 9 in (3, 6)
            A0 = next(-1+M*k for k in range(1, 4) if (-1+M*k) % 9 == 5)
            assert pell_mod(A0, 18, 9) == (1, 0)
            assert pell_mod(A0, e, 3*M)[1] == t % (3*M)
            coefficient = (q**3*((pow(2, e, 3*m)+1)//3)) % m if m > 1 else 0
            assert gcd(coefficient, m) == 1
            s0 = -pow(coefficient, -1, m) % m if m > 1 else 0
            Cmod3 = 4*pow(q, 3, 3)*((pow(2, e, 9)+1)//3) % 3
            z0 = next(z for z in range(3) if (Cmod3*(s0+m*z)+1) % 3 == 2)
            s_base = s0+m*z0
            assert (coefficient*s_base+1) % m == 0
            assert gcd(-3, m) == 1 and gcd(Cmod3*m, 3) == 1
            records.append(dict(D=D, q=q, M=M, t=t, e=e, A_mod_3M=A0 % (3*M),
                s_residue_mod_3m=s_base % (3*m),
                scope='Modular checks only; X=2^e and the prime progression are not expanded.'))
    return records


def lucas_certificate(n):
    """Factorization proposes a certificate; verification never trusts isprime."""
    if n == 2:
        return dict(n=2)
    factors = [(int(p), int(a)) for p, a in sorted(sp.factorint(n-1).items())]
    children = [lucas_certificate(p) for p, _ in factors]
    for base in range(2, n):
        if pow(base, n-1, n) == 1 and all(gcd(pow(base, (n-1)//p, n)-1, n) == 1 for p, _ in factors):
            return dict(n=n, base=base, factors=factors, children=children)
    raise AssertionError('no Lucas certificate')


def verify_lucas(record):
    n = record['n']
    if n == 2:
        return 1
    assert n > 2 and n % 2
    factors, children = record['factors'], record['children']
    assert len({p for p, _ in factors}) == len(factors) == len(children)
    assert all(p >= 2 and a >= 1 for p, a in factors)
    assert prod(p**a for p, a in factors) == n-1
    checked = 1
    for (p, _), child in zip(factors, children):
        assert child['n'] == p
        checked += verify_lucas(child)
    base = record['base']
    assert 1 < base < n and pow(base, n-1, n) == 1
    assert all(gcd(pow(base, (n-1)//p, n)-1, n) == 1 for p, _ in factors)
    return checked


def modular_host():
    # This deliberately small q=2 host is below the full theorem's q>=16.
    q, D, M, e, s = 2, 1, 3, 55, 23
    X, Y = 1 << e, q**3*s
    A = Y*(X+1)+2
    H, E, P = 4*A-5, X*Y, 2*X*Y*Y+1
    ell = H//3
    assert ell == 8839064868652493729 and ell % 3 == 2 and ell > 3*M
    certificate = lucas_certificate(ell)
    prime_nodes = verify_lucas(certificate)
    assert A % M == M-1 and A % 9 == 5 and e % (18*M) == 1
    L = 12*M*(ell-1)
    assert pell_mod(A, L, M*H) == (1, 0)
    assert pow(2, L, H) == 1 and gcd(L, M*H) == 3*M
    assert pell_mod(A, e, 3*M)[1] == 1
    # A large candidate return is accepted only after exact verification.
    TE = E**3*(2**2-1)*(23**2-1)
    assert pell_mod(A, TE, E) == (1, 0)
    rng = random.Random(860001)
    progression_cases = input_cases = 0
    examples = []
    for K in range(2, 82, 2):
        choices = [v for v in wrap_choices(M, K) if v['t'] == 1]
        for choice in choices:
            eps, omega, sigma, j = (choice[key] for key in ('epsilon','omega','input_sign','wrap'))
            u = 3+2*(K % 5)
            v = u if sigma == -1 else A*u
            chi, psi = pell_mod(A, v, M*H)
            Fv_mod = (chi+(A-2)*psi) % (M*H)
            assert Fv_mod % 3 == sigma % 3
            assert pell_mod(A, v, A*A-1)[1] == u
            input_cases += 1
            ce = pell_mod(A, e, M*H)[1]
            initial = (K+2*eps-omega*e+j*ce-M*Fv_mod) % (M*H)
            assert initial % (3*M) == 0
            z = (initial//(3*M))*pow(omega*L//(3*M), -1, ell) % ell
            p0 = e+L*z
            step = lcm(L*ell, E, TE)
            cE = pell_mod(A, p0, E)[1]
            numerator = -eps+omega*p0-j*cE
            assert numerator % 2 == 0
            n0 = (numerator//2) % (E//2)
            for r in (0, 1, rng.randrange(1, 10**20)):
                p = p0+step*r
                c = pell_mod(A, p, M*H)[1]
                assert (K+2*eps-omega*p+j*c-M*Fv_mod) % (M*H) == 0
                assert pow(2, p, H) == X % H and p % 4 == 3
                n = n0+(E//2)*rng.randrange(1, 10**20)
                kE = 2*pell_mod(P, n, E)[1]
                assert (kE-omega*p+j*pell_mod(A, p, E)[1]+eps) % E == 0
                progression_cases += 1
            if len(examples) < 4:
                examples.append(dict(K=K, **choice, u=u, input_index=v, p0=p0,
                                     p_step=step, n0=n0, n_modulus=E//2))
    return dict(q=q,D=D,M=M,e=e,X=X,Y=Y,A=A,H=H,E=E,P=P,ell=ell,
        L=L, Pell_return_E=TE, prime_certificate=certificate,
        recursively_verified_prime_nodes=prime_nodes, progression_checks=progression_cases,
        input_index_checks=input_cases, examples=examples,
        scope='Exact modular fixture only: q=2 is below the candidate theorem domain. '
              'No ratios, positive full zero, actual compiler instance or giant witness is asserted here.')


def mapped_values(data, variables, epsilon, omega, wrap):
    B, q, d, b, x, MC, MF, X, Y = (data[n] for n in ('B','q','d','b','x','MC','MF','X','Y'))
    p,c,k,chi_first,chi_main,kappa,chi_input,f,i,V,y = variables
    a=Y*(X+1); A=a+2; Delta=A*A-1; H=4*a+3; E=X*Y; M=q*q-1
    J = exact_divide(q-1,B-1)
    K=q*(q-2)*M+(MC+q*(MF+B-1))*J
    Fv=chi_input+a*kappa
    rho=exact_divide(K+2*epsilon-omega*p+wrap*c-M*Fv,M*H)
    gamma=exact_divide(chi_main-a*c-X,H)
    values=dict(Jrep=J,F=2,alpha=q-2-2*d*x,zplus=1,f=f,
        h=exact_divide(k-omega*p+wrap*c+epsilon,E),i=i,
        j=exact_divide(V+omega*p-wrap*c,c),o=exact_divide(V+c,f),
        s=exact_divide(Y,q**3),w=exact_divide(X,q**3),
        tau_gap=chi_first-X*Y*Y*k,eta=c-k*Y,zeta=k*(Y+1)-c,y_aux=y,
        Z=rho*H+Fv,delta=exact_divide(kappa-2*d*x-b,Delta),rho=rho,sigma=gamma-rho,
        x=x,B=B,DC=data['DC'],DR=data['DR'],MC=MC,MF=MF,cell_bits=d,inner_bits=b)
    expected=dict(norm_first=chi_first**2-X*Y*Y*(X*Y*Y+1)*k*k,
        norm_main=chi_main**2-Delta*c*c,norm_input=chi_input**2-Delta*kappa*kappa,
        norm_aux=Delta**2*i*i*c**4*(V*V-y*y)+y*y,
        norm_index=epsilon,norm_transport=-1,norm_strong=f*f-Delta*i*i*c**4,
        norm_linear=-epsilon)
    return values,expected


def source_audit():
    symbols=sp.symbols('p c k chi_first chi_main kappa chi_input f i V y',nonzero=True)
    fixtures=[dict(B=32,q=32,d=5,b=5,x=1,MC=6,MF=12,X=32768,Y=98304,DC=3,DR=5),
              dict(B=32,q=32**5,d=5,b=125,x=100,MC=10,MF=20,X=32**15,Y=3*32**15,DC=13,DR=17),
              dict(B=2**25,q=2**25,d=25,b=5,x=7,MC=42,MF=36,X=2**75,Y=5*2**75,DC=29,DR=31)]
    symbolic = numerical = signed = 0
    rng=random.Random(860002)
    for data in fixtures:
        for eps in (-1,1):
            for omega in (-1,1):
                values,expected=mapped_values(data,symbols,eps,omega,6)
                env=candidate.eliminated.run(candidate.sources()[3],candidate.eliminated.fixed_inputs(values))
                for name,expression in expected.items():
                    assert sp.cancel(env[name]-expression)==0,name
                assert sp.cancel(env['polynomial']-(sp.prod(expected.values())-1))==0
                symbolic+=1
                for case in range(16):
                    vals=[Fraction(rng.randrange(1,20)*(-1 if case>=8 and rng.randrange(2) else 1),rng.randrange(1,8)) for _ in symbols]
                    values,expected=mapped_values(data,vals,eps,omega,2*rng.randrange(1,20))
                    env=candidate.eliminated.run(candidate.sources()[3],candidate.eliminated.fixed_inputs(values))
                    assert all(env[n]==v for n,v in expected.items())
                    assert env['polynomial']==prod(expected.values())-1
                    assert not any(isinstance(v,float) for v in values.values())
                    numerical+=1;signed+=case>=8
    return dict(symbolic_complete_eight_factor_and_output_identities=symbolic,
        rational_complete_output_identities=numerical,signed_cases=signed,
        fixtures=fixtures,source=theorem_contract()['source'],
        zero_factor_values_epsilon_minus=[1,1,1,1,-1,-1,1,1],
        zero_factor_values_epsilon_plus=[1,1,1,1,1,-1,1,-1],
        scope='Formal/rational substitutions audit the literal source. These are not asserted positive zeros.')


def verify():
    return dict(status='PASS_PARAMETRIC_ALL_INPUT_COLLAPSE_OF_86',contract=theorem_contract(),
        wrap=wrap_audit(),widths=width_audit(),modular_host=modular_host(),literal_source=source_audit(),
        scope='The accompanying parametric proof uses Dirichlet and irrational rotation. '
              'No actual compiler numeral or full giant witness is materialized. '
              'The separate established75/87 constructions are unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=json.loads(json.dumps(verify()))
    path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['contract']['conclusion']);print(result['scope'])
