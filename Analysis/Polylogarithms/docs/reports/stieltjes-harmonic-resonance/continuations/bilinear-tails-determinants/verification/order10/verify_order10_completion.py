"""Exact completion of order-ten centered harmonic-tail reconstruction.

Python 3 and SymPy; no floating-point arithmetic or network access is used.
The inherited P10 coefficient certificate is independently replayed by --full.
The new modulus-2**17 identity is checked coefficientwise on every run.
Two unrelated Bernoulli computations and a direct five-square determinant
also verify the formerly exceptional index b=962 modulo 2**32.

Inherited normalization: ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11,
Section 7. The displayed Newton determinant is reimplemented below.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import time

import sympy as s
from sympy.polys.domains import QQ
from sympy.polys.rings import ring

ROOT = Path(__file__).resolve().parent
MOD = 1 << 17
B17 = [1, 20068, -26384, 2816, 45824, 4096, -24576, 0, 65536]
R17 = [694, -1831, -1930, -1696, 464, -816, -928, 128, 1536]


def v2(n):
    n = abs(int(n))
    if not n:
        raise ValueError('v2(0) is not finite')
    return (n & -n).bit_length()-1


def falling(x, n):
    return math.prod(x-j for j in range(n))


def poly_mul(a, b, mod):
    out = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j]+x*y) % mod
    return out


def poly_pow(a, n, mod):
    out = [1]
    for _ in range(n):
        out = poly_mul(out, a, mod)
    return out


def shifted(poly, shift, mod):
    return [sum(c*math.comb(j, k)*shift**(j-k)
                for j, c in enumerate(poly) if j >= k) % mod
            for k in range(len(poly))]


def eval_poly(poly, x, mod=None):
    out = 0
    for c in reversed(poly):
        out = out*x+c
        if mod:
            out %= mod
    return out


def coefficient_congruence(terms):
    # Group by the nine U exponents; all b coefficients remain exact.
    groups = defaultdict(dict)
    for ex, coeff in terms:
        groups[tuple(ex[1:])][ex[0]] = int(coeff)
    powers = [[poly_pow(shifted(B17, -j, MOD), k, MOD)
               for k in range(6)] for j in range(1, 10)]
    observed = [0]
    for ex, coefficients in groups.items():
        term = [coefficients.get(i, 0) % MOD
                for i in range(max(coefficients)+1)]
        for j, power in enumerate(ex):
            if power:
                term = poly_mul(term, powers[j][power], MOD)
        if len(term) > len(observed):
            observed += [0]*(len(term)-len(observed))
        observed = [(observed[i]+(term[i] if i < len(term) else 0)) % MOD
                    for i in range(len(observed))]
    assert all(value == (32*R17[i] % MOD if i < len(R17) else 0)
               for i, value in enumerate(observed))
    assert R17[1] % 2 == 1
    assert all(c % 2 == 0 for c in R17[2:])
    assert eval_poly(R17, 3010, 4096) == 0
    assert eval_poly(R17, 962, 4096) == 2048
    return {'input_monomials': len(terms), 'U_monomial_groups': len(groups),
            'coefficient_positions_checked': len(observed),
            'root_mod_4096': 3010, 'root_is_unique_by_odd_difference_quotient': True}


def bernoulli_polynomial_check():
    x = s.Symbol('x')
    # K=17, s=9, J=8 in the finite Faulhaber argument.
    avg = s.Poly(s.expand(sum(
        s.Rational(sum((v*v-1)**j for v in range(1, 512, 2)), 256)
        *s.prod(x-k for k in range(j))/s.factorial(j)
        for j in range(9))), x)
    for j in range(9):
        coeff = avg.nth(j)
        assert int(coeff.q) % 2 == 1
        assert int(coeff.p)*pow(int(coeff.q), -1, MOD) % MOD == B17[j] % MOD
    diagnostics = []
    for m in range(13, 65):
        val = 2*s.bernoulli(2*m)
        residue = int(val.p)*pow(int(val.q), -1, MOD) % MOD
        assert residue == eval_poly(B17, m, MOD)
        diagnostics.append(m)
    return {'finite_average_terms': 9, 'odd_support_points': 256,
            'uniform_threshold': 13, 'independent_rational_diagnostics': diagnostics}


def doubled_bernoulli_recurrence(max_m, mod):
    values = [2]
    for m in range(1, max_m+1):
        n = 2*m+1
        coef = n*(n-1)//2
        total = 2*m-1
        for j in range(1, m):
            total -= coef*values[j]
            k = 2*j
            coef = coef*(n-k)*(n-k-1)//((k+1)*(k+2))
        values.append(total*pow(n, -1, mod) % mod)
    return values


def doubled_bernoulli_power_sum(m, precision=32):
    width = (precision+1)//2
    workmod = 1 << (precision+width-1)
    total = sum(pow(v, 2*m, workmod) for v in range(1, 1 << width, 2)) % workmod
    assert total % (1 << (width-1)) == 0
    return total >> (width-1)


def determinant_fraction(matrix):
    mat = [[Fraction(x) for x in row] for row in matrix]
    sign = 1
    result = Fraction(1)
    for k in range(len(mat)):
        pivot = next((i for i in range(k, len(mat)) if mat[i][k]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != k:
            mat[k], mat[pivot] = mat[pivot], mat[k]
            sign = -sign
        val = mat[k][k]
        result *= val
        for i in range(k+1, len(mat)):
            multiplier = mat[i][k]/val
            for j in range(k+1, len(mat)):
                mat[i][j] -= multiplier*mat[k][j]
    return sign*result


def numeric_small_matrix(b, Us):
    a = 5
    F = [[Fraction(0) for _ in range(a)] for _ in range(a)]
    A = [[Fraction(0) for _ in range(a)] for _ in range(a)]
    for i in range(a):
        n = b-a+i
        W = lambda y: (2*n+2-y)*falling(4*n+2-y, 2*i)
        d = {h: Fraction(sum((-1)**(h-j)*math.comb(h, j)*W(j)
                            for j in range(h+1)), math.factorial(h))
             for h in range(1, 2*i+2, 2)}
        for ell in range(a):
            N, R = 2*(n-ell)+1, 2*b-2*a+2+2*ell
            F[i][ell] = Fraction(math.prod((2*n-r)*(2*n+3+r)
                                          for r in range(2*ell)),
                                   math.factorial(2*ell+1))
            diff = R-N
            rat = (Fraction(math.prod(N+j for j in range(1, diff+1)))
                   if diff >= 0 else
                   Fraction(1, math.prod(R+j for j in range(1, -diff+1))))
            factor = rat / ((2*n+1)*(2*n+2)*math.factorial(2*ell+2))
            A[i][ell] = 2*F[i][ell] + factor*sum(
                d[h]*falling(N, h)*Us[a-i+ell+(h-1)//2-1] for h in d)
    return F, A


def D10(b):
    return eval_poly([1488375, 4244400, -2571948, -15838992,
                      -4469984, 24490080, 14925056, -38140416,
                      23705088, -7303680, 1236992, -110592, 4096], b)


def certificate_evaluate(terms, b, Us, mod):
    vals = [b, *Us]
    powers = [[pow(v, i, mod) for i in range(25)] for v in vals]
    out = 0
    for ex, c in terms:
        term = int(c)
        for i, e in enumerate(ex):
            term = term*powers[i][e] % mod
        out = (out+term) % mod
    return out


def isolated_case(terms):
    b = 962
    mod = 1 << 32
    values = doubled_bernoulli_recurrence(b-1, mod)
    U = [values[b-j] for j in range(1, 10)]
    independent = [doubled_bernoulli_power_sum(b-j) for j in range(1, 10)]
    assert U == independent
    residue = certificate_evaluate(terms, b, U, mod)
    F, A = numeric_small_matrix(b, U)
    direct = 138240*(2*b-7)*(2*b-5)*D10(b)*determinant_fraction(A)/determinant_fraction(F)
    assert direct.denominator == 1
    assert direct.numerator % mod == residue == 2386755584
    assert v2(residue) == 16
    return {'b': b, 'modulus': mod, 'doubled_Bernoulli_residues': U,
            'numerator_residue': residue, 'numerator_valuation': 16,
            'determinant_ratio_valuation': 6,
            'independent_Bernoulli_power_sums_agree': True,
            'direct_five_square_determinant_agrees': True}


def base_cases():
    out = []
    for b in range(6, 23):
        mu = [s.bernoulli(2*j)/s.factorial(2*j) for j in range(2*b-5)]
        def entry(i, k):
            ix = i+k-4
            if ix < 0:
                return s.S.Zero
            return mu[ix]*(s.factorial(2*b+2*i-9)/s.factorial(2*b-2*k)
                    +(s.factorial(2*i+1)/s.factorial(10-2*k) if k < 5 else 0))
        mat = s.Matrix(b, b, entry)
        det = mat.det(method='domain-ge')
        assert det != 0
        out.append({'b': b, 'det_M': str(det),
                    'v2_det_M': v2(det.p)-v2(det.q)})
    return out


def threshold_arithmetic():
    # The coefficient norm is independently regenerated by eventual_threshold.py.
    norm_E = 602847821074996042728613866361551228764160
    K = 120*norm_E**5
    kappa = 14932726824960000000
    V = Fraction(2401, 36864000000000000)
    C = Fraction(K*8**26*2**64, kappa*4**5*V*120**18)
    b = 1920
    bound = C*b**64*960**(2*b)/math.factorial(2*b-18)
    assert bound*(1 << 546) < 1
    ratio = Fraction(b+1, b)**64*Fraction(960**2, (2*b-16)*(2*b-17))
    assert ratio < Fraction(3, 4)
    return {'coefficient_norm_E': norm_E, 'kappa': kappa, 'V': str(V),
            'constant_C': str(C), 'threshold_b': b,
            'bound_at_threshold_less_than': '2^(-546)',
            'exact_successive_ratio_at_threshold': str(ratio)}


def symbolic_source_replay(data):
    b, y = s.symbols('b y')
    Us = s.symbols('U1:10')
    F, A = s.zeros(5), s.zeros(5)
    for i in range(5):
        n = b-5+i
        W = (2*n+2-y)*s.prod(4*n+2-y-r for r in range(2*i))
        d = {h: s.expand(sum((-1)**(h-j)*s.binomial(h, j)*W.subs(y, j)
                             for j in range(h+1))/s.factorial(h))
             for h in range(1, 2*i+2, 2)}
        for ell in range(5):
            N, R = 2*(n-ell)+1, 2*b-8+2*ell
            F[i, ell] = s.prod((2*n-r)*(2*n+3+r) for r in range(2*ell))/s.factorial(2*ell+1)
            diff = 1+4*ell-2*i
            ratio = (s.prod(N+j for j in range(1, diff+1)) if diff >= 0 else
                     1/s.prod(R+j for j in range(1, -diff+1)))
            A[i, ell] = s.factor(2*F[i, ell] + ratio*sum(
                d[h]*s.prod(N-r for r in range(h))*Us[5-i+ell+(h-1)//2-1]
                for h in d)/((2*n+1)*(2*n+2)*s.factorial(2*ell+2)))
    symbols = {'b': b, **{str(u): u for u in Us}}
    den = s.sympify(data['denominator'], locals=symbols)
    fdet = s.sympify(data['F_determinant'], locals=symbols)
    assert s.cancel(F.det(method='domain-ge')-fdet) == 0
    P = s.Poly.from_dict({tuple(ex): s.Integer(c) for ex, c in data['numerator_terms']},
                         (b, *Us), domain=s.ZZ).as_expr()
    R, *_ = ring([b, *Us], QQ)
    rowden = [s.lcm([s.denom(A[i, j]) for j in range(5)]) for i in range(5)]
    entries = [[R.from_expr(s.cancel(rowden[i]*A[i, j])) for j in range(5)] for i in range(5)]
    determinant = R.zero
    for perm in itertools.permutations(range(5)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(5) for j in range(i+1, 5))
        term = R(sign)
        for i, j in enumerate(perm):
            term *= entries[i][j]
        determinant += term
    assert determinant*R.from_expr(den) == R.from_expr(P)*R.from_expr(s.expand(fdet*s.prod(rowden)))
    return {'signed_permutation_products': 120,
            'cleared_determinant_monomials': len(determinant),
            'inherited_certificate_rebuilt_from_Newton_matrix': True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true', help='also rebuild the inherited multivariate identity')
    parser.add_argument('--certificate', type=Path, default=ROOT/'rank_ten_certificate_grouped.json')
    parser.add_argument('--output', type=Path, default=ROOT/'order10_completion_checks.json')
    args = parser.parse_args()
    start = time.perf_counter()
    data = json.loads(args.certificate.read_text())
    if 'numerator_groups' in data:
        data['numerator_terms'] = [([power, *group['U_exponents']], int(coefficient))
            for group in data['numerator_groups']
            for power, coefficient in enumerate(group['b_coefficients']) if coefficient]
    assert len(data['numerator_terms']) == 10403
    result = {'claim': 'M_(5,b) is nonsingular for every integer b>=6.',
              'new_uniform_Bernoulli_polynomial': B17,
              'new_numerator_residue_polynomial': R17,
              'modulus': MOD,
              'Bernoulli_polynomial_check': bernoulli_polynomial_check(),
              'polynomial_identity_check': coefficient_congruence(data['numerator_terms']),
              'isolated_case_independent_audit': isolated_case(data['numerator_terms']),
              'direct_source_base_cases': base_cases(),
              'eventual_threshold_arithmetic': threshold_arithmetic()}
    if args.full:
        print('Rebuilding the inherited five-square symbolic determinant.', flush=True)
        result['full_source_replay'] = symbolic_source_replay(data)
    result['status'] = 'all exact checks passed'
    result['elapsed_seconds'] = round(time.perf_counter()-start, 3)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'elapsed_seconds': result['elapsed_seconds'],
                      'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
