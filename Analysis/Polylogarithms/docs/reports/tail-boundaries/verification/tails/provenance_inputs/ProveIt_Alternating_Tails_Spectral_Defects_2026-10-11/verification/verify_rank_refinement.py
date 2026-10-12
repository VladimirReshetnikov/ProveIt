"""Rebuild and verify the order-eight refinement and new order-ten certificate.

Run with Python 3 and SymPy. No network, floating-point arithmetic, or fitted
formulas are used. The full multivariate determinant check may take 1--3 minutes.
The JSON numerators are finite certificates, not inputs to the source-matrix
base calculations. `--quick` omits only the multivariate determinant replays.
"""
from __future__ import annotations
import argparse
import collections
import itertools
import json
import time
from pathlib import Path
import sympy as s
from sympy.polys.domains import QQ
from sympy.polys.rings import ring

ROOT = Path(__file__).resolve().parent
DATA = ROOT.parent/'data'
if not (DATA/'rank_eight_certificate.json').exists():
    DATA = ROOT

def falling(x, k):
    return s.prod(x-j for j in range(k))

def factorial_ratio(upper, lower, difference):
    if difference >= 0:
        return s.prod(lower+j for j in range(1, difference+1))
    return 1/s.prod(upper+j for j in range(1, -difference+1))

def build_matrices(a, b, Us):
    z = s.Symbol('z')
    F, A = s.zeros(a), s.zeros(a)
    for i in range(a):
        n = b-a+i
        for ell in range(a):
            N, R = 2*(n-ell)+1, 2*b-2*a+2+2*ell
            F[i,ell] = s.factor(s.prod((2*n-r)*(2*n+3+r)
                for r in range(2*ell))/s.factorial(2*ell+1))
            W = (z+2*ell+1)*falling(2*n+2*ell+z+1, 2*i)
            total = 0
            for h in range(1, 2*i+2, 2):
                d = s.expand(sum((-1)**(h-j)*s.binomial(h,j)
                    *W.subs(z,N-j) for j in range(h+1))/s.factorial(h))
                index = a-i+ell+(h-1)//2
                total += d*falling(N,h)*Us[index-1]
            factor = factorial_ratio(R,N,1+4*ell-2*i)/(
                (2*n+1)*(2*n+2)*s.factorial(2*ell+2))
            A[i,ell] = s.factor(2*F[i,ell]+factor*total)
    return F, A

def replay_polynomial_identity(a, b, Us, P, denominator, Fdet):
    F, A = build_matrices(a,b,Us)
    assert s.cancel(F.det(method='domain-ge')-Fdet) == 0
    R, *_ = ring([b,*Us],QQ)
    row_den = [s.lcm([s.denom(A[i,j]) for j in range(a)]) for i in range(a)]
    entries = [[R.from_expr(s.cancel(row_den[i]*A[i,j]))
                for j in range(a)] for i in range(a)]
    determinant = R.zero
    for perm in itertools.permutations(range(a)):
        inversions = sum(perm[i]>perm[j] for i in range(a) for j in range(i+1,a))
        term = R((-1)**inversions)
        for i,j in enumerate(perm):
            term *= entries[i][j]
        determinant += term
    left = determinant*R.from_expr(denominator)
    right = R.from_expr(P)*R.from_expr(s.expand(Fdet*s.prod(row_den)))
    assert left == right
    return {'signed_permutation_products':s.factorial(a).__int__(),
            'cleared_determinant_terms':len(determinant)}

def polynomial_groups(P,b,Us):
    poly = s.Poly(P,b,*Us,domain=s.ZZ)
    groups = collections.defaultdict(dict)
    for ex,c in poly.terms():
        groups[ex[1:]][ex[0]] = int(c)
    return groups

def poly_add(p,q,M):
    out = p+[0]*max(0,len(q)-len(p))
    for i,c in enumerate(q):
        out[i] = (out[i]+c)%M
    return out

def poly_mul(p,q,M):
    out = [0]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        if c:
            for j,d in enumerate(q):
                out[i+j] = (out[i+j]+c*d)%M
    return out

def poly_power(p,k,M):
    out = [1]
    for _ in range(k):
        out = poly_mul(out,p,M)
    return out

def substitute_mod(groups, substitutions, degree, M):
    powers = [[poly_power(v,k,M) for k in range(degree+1)] for v in substitutions]
    out = [0]
    for ex,coefficients in groups.items():
        term = [coefficients.get(i,0)%M for i in range(max(coefficients)+1)]
        for j,e in enumerate(ex):
            if e:
                term = poly_mul(term,powers[j][e],M)
        out = poly_add(out,term,M)
    return out

def source_determinant(a,b):
    def mu(j):
        return s.bernoulli(2*j)/s.factorial(2*j) if j>=0 else s.S.Zero
    M = s.Matrix(b,b,lambda t,k:mu(t+k-a+1)*(
        s.factorial(2*b+2*t-2*a+1)/s.factorial(2*b-2*k)
        +(s.factorial(2*t+1)/s.factorial(2*a-2*k) if k<a else 0)))
    H = s.Matrix(b,b,lambda t,k:mu(t+k-a+1))
    md, hd = M.det(method='domain-ge'), H.det(method='domain-ge')
    scale = s.prod(s.factorial(2*b+2*t-2*a+1) for t in range(b))
    scale /= s.prod(s.factorial(2*b-2*k) for k in range(b))
    return md, s.cancel(md/(hd*scale))

def valuation2(x):
    n,d = s.fraction(x)
    assert n != 0
    return (int(n)&-int(n)).bit_length()-(int(d)&-int(d)).bit_length()

def evaluate_certificate(groups,a,b,denominator,b_symbol):
    powers = [[(2*s.bernoulli(2*b-2*j))**k for k in range(a+1)]
              for j in range(1,2*a)]
    numerator = s.S.Zero
    for ex,coefficients in groups.items():
        term = sum(c*b**i for i,c in coefficients.items())
        for j,e in enumerate(ex):
            term *= powers[j][e]
        numerator += term
    return s.cancel(numerator/denominator.subs(b_symbol,b))

def main():
    started = time.perf_counter()
    parser = argparse.ArgumentParser()
    parser.add_argument('--quick',action='store_true')
    args = parser.parse_args()
    x = s.Symbol('x')
    B16 = (1+20068*x-26384*x**2+2816*x**3-19712*x**4
           +4096*x**5-24576*x**6)
    average = s.expand(sum(s.Rational(sum((v*v-1)**j
        for v in range(1,256,2)),128)*falling(x,j)/s.factorial(j)
        for j in range(8)))
    for c in s.Poly(average-B16,x).all_coeffs():
        assert c.q%2 == 1
        assert int(c.p)*pow(int(c.q),-1,65536)%65536 == 0
    # Finite rational diagnostics for the independently proved uniform lemma.
    for m in range(12,81):
        difference = 2*s.bernoulli(2*m)-B16.subs(x,m)
        assert difference == 0 or valuation2(difference)>=16
    summary = {'Bernoulli_modulus':65536,'Bernoulli_polynomial':str(B16),
               'Bernoulli_threshold':12,'families':{},'status':'exact checks passed'}
    bases = json.loads((DATA/'direct_rank_checks.json').read_text())
    for name,a,L,root_residue in [('eight',4,14,8001),('ten',5,11,962)]:
        data = json.loads((DATA/f'rank_{name}_certificate.json').read_text())
        b = s.Symbol('b')
        Us = s.symbols('U1:'+str(2*a))
        symbols = {'b':b,**{str(u):u for u in Us}}
        P = s.Poly.from_dict({tuple(ex):s.Integer(c) for ex,c in data['numerator_terms']}, (b,*Us), domain=s.ZZ).as_expr()
        denominator = s.sympify(data['denominator'],locals=symbols)
        Fdet = s.sympify(data['F_determinant'],locals=symbols)
        groups = polynomial_groups(P,b,Us)
        results = {'integer_polynomial_terms':len(s.Poly(P,b,*Us).terms()),
                   'U_monomials':len(groups)}
        if not args.quick:
            print(f'Rebuilding order {2*a} polynomial identity',flush=True)
            results.update(replay_polynomial_identity(a,b,Us,P,denominator,Fdet))
        if a==4:
            residue_polynomial = (4096*b**9-5120*b**8+4864*b**7+2176*b**6
                -176*b**5-5184*b**4-4912*b**3-7948*b**2+1195*b-1727)
            multiplier, denom_val = 4,6
        else:
            residue_polynomial = (-512*b**8+128*b**7-928*b**6-816*b**5
                +464*b**4+352*b**3+118*b**2+217*b+694)
            multiplier, denom_val = 32,10
        substitutions = []
        for j in range(1,2*a):
            pp = s.Poly(B16.subs(x,b-j),b)
            substitutions.append([int(pp.nth(i))%65536 for i in range(7)])
        observed = substitute_mod(groups,substitutions,a,65536)
        target = s.Poly(multiplier*residue_polynomial,b)
        assert all(c%65536 == int(target.nth(i))%65536
                   for i,c in enumerate(observed))
        assert all(int(target.nth(i))%65536==0
                   for i in range(len(observed),target.degree()+1))
        rp = s.Poly(residue_polynomial,b)
        assert rp.nth(1)%2==1
        assert all(rp.nth(i)%2==0 for i in range(2,rp.degree()+1))
        assert residue_polynomial.subs(b,root_residue)%2**L==0
        results.update({'residue_polynomial':str(residue_polynomial),
            'exceptional_residue':root_residue,'exceptional_modulus':2**L,
            'large_b_threshold':2*a+11,'denominator_valuation':denom_val})
        # Source matrices supply all finite base cases required by the theorem.
        source_values = [17] if a==4 else list(range(6,21))
        exact_bases = []
        for bv in source_values:
            md,rho = source_determinant(a,bv)
            assert md!=0 and rho!=0
            recorded = next(row for row in bases if row['a']==a and row['b']==bv)
            assert md == s.Rational(recorded['Mdet'])
            assert rho == s.Rational(recorded['rho'])
            if bv>=2*a:
                assert evaluate_certificate(groups,a,bv,denominator,b)==rho
            exact_bases.append({'b':bv,'Mdet':str(md),'rho':str(rho),
                                'valuation':valuation2(rho)})
        results['finite_bases'] = exact_bases
        # Check normalization above the Bernoulli threshold independently.
        bv = 2*a+11
        md,rho = source_determinant(a,bv)
        assert evaluate_certificate(groups,a,bv,denominator,b)==rho
        results['large_source_crosscheck'] = {'b':bv,'valuation':valuation2(rho)}
        summary['families'][str(2*a)] = results
        print(f'Order {2*a}: all exact identities and base cases passed',flush=True)
    output_name = 'rank_refinement_quick_checks.json' if args.quick else 'rank_refinement_checks.json'
    summary['elapsed_seconds'] = round(time.perf_counter()-started,3)
    summary['full_replay'] = not args.quick
    (DATA/output_name).write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':summary['status'],'full_replay':not args.quick,
        'output':str(DATA/output_name),
        'elapsed_seconds':summary['elapsed_seconds'],'exceptional_classes':
        {'8':'b = 8001 mod 16384','10':'b = 962 mod 2048'}},indent=2))

if __name__=='__main__':
    main()
