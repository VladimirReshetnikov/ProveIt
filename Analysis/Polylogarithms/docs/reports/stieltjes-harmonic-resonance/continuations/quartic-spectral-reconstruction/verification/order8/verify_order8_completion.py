"""Exact verification for complete order-eight harmonic-tail reconstruction.

The proof has an analytic infinite-range step, proved in the article. This
script verifies its finite inputs: the inherited determinant identity, the
new highest-degree Hankel factor, every explicit integer constant, the
uniform-bound base case, and every remaining finite exceptional index.
No floating-point comparison is used as a proof gate.

Requires Python 3.10+ and SymPy. Run beside rank_eight_certificate.json and
verify_rank_eight_source.py. Use --skip-source only if that inherited
certificate has already been independently replayed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import importlib.util
import json
import math
from pathlib import Path
import sympy as sp


def doubled_bernoulli_mod(maximum: int, modulus: int) -> list[int]:
    """Independent finite recurrence, with only odd modular divisors."""
    residues = [0] * (maximum + 1)
    for m in range(1, maximum + 1):
        numerator = 2*m - 1
        for j in range(1, m):
            numerator -= math.comb(2*m+1, 2*j) * residues[j]
        residues[m] = numerator * pow(2*m+1, -1, modulus) % modulus
    return residues


def evaluate_grouped_mod(grouped, b_value, U_values, modulus):
    total = 0
    for powers, coefficient in grouped:
        term = int(coefficient.eval(b_value)) % modulus
        for value, power in zip(U_values, powers):
            term = term * pow(value, power, modulus) % modulus
        total = (total + term) % modulus
    return total


def run(certificate_path: Path, rebuild_source: bool):
    certificate = json.loads(certificate_path.read_text())
    source_replay = None
    if rebuild_source:
        source_script = Path(__file__).with_name('verify_rank_eight_source.py')
        spec = importlib.util.spec_from_file_location('order8_source', source_script)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        source_replay = module.run(certificate)

    b = sp.Symbol('b')
    U = sp.symbols('U1:8')
    P = sp.Poly(sp.sympify(certificate['numerator']), b, *U, domain=sp.ZZ)
    grouped_P = sp.Poly(P.as_expr(), *U)
    assert max(sum(powers[1:]) for powers, _ in P.terms()) == 4

    G = (12288*(b-6)**4*(b-5)**4*(b-4)**4*(b-3)**3*(b-2)**2*(b-1)
         *(2*b-13)**4*(2*b-11)**4*(2*b-9)**4*(2*b-7)**3
         *(2*b-5)**3*(2*b-3)**2*(2*b-1))
    hankel = sp.Poly(sp.Matrix(4, 4, lambda i,j: U[i+j]).det(), *U)
    quartic = {powers:c for powers,c in grouped_P.terms() if sum(powers)==4}
    assert len(quartic) == 16
    assert set(quartic) == set(dict(hankel.terms()))
    for powers, coefficient in hankel.terms():
        alpha_product = sp.S.One
        for j, power in enumerate(powers, 1):
            alpha_product *= sp.prod(2*b-14+r for r in range(1, 15-2*j))**power
        assert sp.cancel(quartic[powers]*alpha_product-G*coefficient) == 0

    # Independent determinant factor from the Newton triangularization.
    structural_scalar = sp.S.One
    for i in range(4):
        n = b-4+i
        rho = 1/((2*n+1)*(2*n+2))
        sigma = sp.prod(2*b-14+r for r in range(1, 9+2*i))/sp.factorial(2*i+2)
        diagonal = -(i+1)*sp.prod(4*n+2-r for r in range(2*i))
        structural_scalar *= rho*sigma*diagonal
    denominator = sp.sympify(certificate['denominator'])
    F_det = sp.sympify(certificate['F_determinant'])
    assert sp.cancel(denominator*structural_scalar/F_det-G) == 0
    print('Highest-degree Hankel factor verified by two exact calculations.', flush=True)

    lower_terms = [(powers,c) for powers,c in P.terms() if sum(powers[1:])<=3]
    K = sum(abs(int(c)) for _,c in lower_terms)
    assert K == 1465775272343372
    assert max(powers[0] for powers,_ in lower_terms) == 15
    points = [Fraction(1,j*j) for j in range(1,5)]
    V = math.prod((points[j]-points[i])**2 for i in range(4) for j in range(i+1,4))
    assert V == Fraction(30625,48922361856)
    C = Fraction(K*2**73, 3*V*24**14)
    assert C == Fraction(211240479050703917773579966480384,602791875)
    R512 = C*512**12*192**1024/math.factorial(1010)
    assert R512 < Fraction(1,2**675)
    assert Fraction(513,512)**12 < 2
    assert 2*192**2 < 1011*1012
    assert math.factorial(20) > 8**20
    print('All constants and the uniform infinite-range base comparison verified.', flush=True)

    grouped = [(powers,sp.Poly(c,b,domain=sp.ZZ)) for powers,c in grouped_P.terms()]
    modulus = 2**32
    bernoulli_residues = doubled_bernoulli_mod(496, modulus)
    finite = []
    rho17 = None
    for bb in range(17,512,16):
        mod_values = [bernoulli_residues[bb-j] for j in range(1,8)]
        residue = evaluate_grouped_mod(grouped,bb,mod_values,modulus)
        assert residue != 0
        # Independent exact-rational Bernoulli calculation and comparison.
        rational_values = [2*sp.bernoulli(2*(bb-j)) for j in range(1,8)]
        value = sum(coefficient.eval(bb)*sp.prod(rational_values[i]**powers[i]
                    for i in range(7)) for powers,coefficient in grouped)
        num, den = value.as_numer_denom()
        assert int(den) % 2
        rational_residue = int(num)*pow(int(den),-1,modulus) % modulus
        assert rational_residue == residue
        valuation = (residue & -residue).bit_length()-1
        finite.append({'b':bb,'P_mod_2_to_32':residue,'v2_P':valuation})
        if bb == 17:
            rho17 = sp.cancel(value/denominator.subs(b,bb))
            assert rho17 == -sp.Rational(5564518155020169678178976040991,8937041637533625)
    assert len(finite)==31
    print('All 31 exceptional indices verified by modular and rational methods.', flush=True)
    return {
        'all_exact_checks_passed':True,
        'theorem':'For every integer b>=5, M_(4,b) is nonsingular; p=8, q=2b optimal prefix.',
        'source_replay':source_replay,
        'quartic_hankel_monomials_verified':16,
        'G_factor':str(G),
        'lower_integer_coefficient_norm_K':K,
        'lower_degree_in_b':15,
        'vandermonde_square_V':str(V),
        'uniform_bound_constant_C':str(C),
        'uniform_threshold':512,
        'exact_uniform_base_bound':'R_512 < 2^(-675)',
        'finite_exception_methods':['odd-divisor Bernoulli recurrence modulo 2^32',
                                    'independent exact rational Bernoulli evaluation'],
        'finite_exceptions':finite,
        'first_new_ratio_rho17':str(rho17),
        'scope_limit':'This completes order eight; general larger smaller-order pairs remain open.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate',type=Path,
                        default=Path(__file__).with_name('rank_eight_certificate.json'))
    parser.add_argument('--output',type=Path,
                        default=Path(__file__).with_name('order8_completion_checks.json'))
    parser.add_argument('--skip-source',action='store_true')
    args = parser.parse_args()
    result = run(args.certificate,not args.skip_source)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':True,'output':str(args.output)},indent=2))


if __name__ == '__main__':
    main()
