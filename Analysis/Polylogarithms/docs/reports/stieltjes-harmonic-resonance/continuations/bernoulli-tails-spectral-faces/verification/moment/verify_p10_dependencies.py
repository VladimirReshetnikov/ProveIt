"""Replay the inherited order-ten congruence and every small base matrix.

The full mode also reconstructs the complete 5x5 polynomial determinant.
--quick skips only that reconstruction. Both modes use exact arithmetic.
"""
from pathlib import Path
import argparse
import json
import time
import sympy as s
from p10_dependency_algebra import (
    falling, replay_polynomial_identity, polynomial_groups, substitute_mod,
    source_determinant, valuation2, evaluate_certificate,
)


def main():
    started=time.perf_counter()
    parser=argparse.ArgumentParser()
    parser.add_argument('--quick',action='store_true')
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    data=json.loads((root/'p10_dependency_certificate.json').read_text())
    b,x=s.symbols('b x')
    Us=s.symbols('U1:10')
    symbols={'b':b,**{str(u):u for u in Us}}
    P=s.Poly.from_dict({tuple(ex):s.Integer(c) for ex,c in data['numerator_terms']},
                       (b,*Us),domain=s.ZZ).as_expr()
    denominator=s.sympify(data['denominator'],locals=symbols)
    Fdet=s.sympify(data['F_determinant'],locals=symbols)
    groups=polynomial_groups(P,b,Us)
    result={'full_polynomial_reconstruction':not args.quick,
            'integer_monomials':len(data['numerator_terms']),
            'U_monomials':len(groups)}
    if not args.quick:
        result.update(replay_polynomial_identity(5,b,Us,P,denominator,Fdet))
    B16=1+20068*x-26384*x**2+2816*x**3-19712*x**4+4096*x**5-24576*x**6
    average=s.expand(sum(s.Rational(sum((v*v-1)**j for v in range(1,256,2)),128)
                        *falling(x,j)/s.factorial(j) for j in range(8)))
    for coefficient in s.Poly(average-B16,x).all_coeffs():
        assert coefficient.q%2==1
        assert int(coefficient.p)*pow(int(coefficient.q),-1,65536)%65536==0
    R=-512*b**8+128*b**7-928*b**6-816*b**5+464*b**4+352*b**3+118*b**2+217*b+694
    substitutions=[]
    for j in range(1,10):
        poly=s.Poly(B16.subs(x,b-j),b)
        substitutions.append([int(poly.nth(i))%65536 for i in range(7)])
    observed=substitute_mod(groups,substitutions,5,65536)
    target=s.Poly(32*R,b)
    assert all(c%65536==int(target.nth(i))%65536 for i,c in enumerate(observed))
    assert all(int(target.nth(i))%65536==0 for i in range(len(observed),target.degree()+1))
    rp=s.Poly(R,b)
    assert rp.nth(1)%2==1
    assert all(rp.nth(i)%2==0 for i in range(2,rp.degree()+1))
    assert R.subs(b,962)%2048==0
    expected=[-4,-4,-6,-5,-2,-5,-4,-5,-3,-5,-4,-5,-1,-5,-4]
    bases=[]
    for bv,valuation in zip(range(6,21),expected):
        md,rho=source_determinant(5,bv)
        assert md!=0 and valuation2(rho)==valuation
        if bv>=10:
            assert evaluate_certificate(groups,5,bv,denominator,b)==rho
        bases.append({'b':bv,'det_M':str(md),'rho':str(rho),'valuation_rho':valuation})
    md,rho=source_determinant(5,21)
    assert evaluate_certificate(groups,5,21,denominator,b)==rho
    result.update({'Bernoulli_average_coefficients_verified':True,
                   'P10_substitution_congruence_verified':True,
                   'residue_polynomial':str(R),
                   'exceptional_residue':962,'exceptional_modulus':2048,
                   'bases':bases,'large_source_crosscheck':{'b':21,'rho':str(rho)},
                   'all_checks_exact':True,
                   'elapsed_seconds':round(time.perf_counter()-started,3)})
    name='p10_dependency_quick_check.json' if args.quick else 'p10_dependency_verification.json'
    (root/name).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['full_polynomial_reconstruction','integer_monomials','U_monomials','all_checks_exact','elapsed_seconds']},indent=2))


if __name__=='__main__':
    main()
