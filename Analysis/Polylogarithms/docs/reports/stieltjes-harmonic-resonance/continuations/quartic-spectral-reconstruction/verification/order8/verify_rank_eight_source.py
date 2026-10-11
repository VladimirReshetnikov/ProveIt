"""Replay the order-eight optimal-prefix certificate using exact arithmetic.

The four-by-four matrix is rebuilt from finite differences of the source
Bernoulli weight.  The determinant identity is checked by 24 permutation
products in ZZ[b,U1,...,U7], after clearing row denominators.  There is no
interpolation and no numerical linear algebra.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import sympy as sp


def falling(x, count):
    return sp.prod(x-j for j in range(count))


def factorial_ratio(x, y, integer_difference):
    if integer_difference >= 0:
        return sp.prod(y+j for j in range(1,integer_difference+1))
    return 1/sp.prod(x+j for j in range(1,-integer_difference+1))


def rebuilt_matrices(b, U):
    z = sp.Symbol("z")
    F = sp.zeros(4)
    A = sp.zeros(4)
    for i in range(4):
        n=b-4+i
        for ell in range(4):
            N=2*(n-ell)+1
            R=2*b-6+2*ell
            F[i,ell]=sp.prod((2*n-j)*(2*n+3+j) for j in range(2*ell))/sp.factorial(2*ell+1)
            W=(z+2*ell+1)*falling(2*n+2*ell+z+1,2*i)
            correction=0
            for h in range(1,2*i+2,2):
                d=sp.expand(sum((-1)**(h-j)*sp.binomial(h,j)*W.subs(z,N-j)
                                for j in range(h+1))/sp.factorial(h))
                index=4-i+ell+(h-1)//2
                correction += d*falling(N,h)*U[index-1]
            prefactor=factorial_ratio(R,N,1+4*ell-2*i)/(
                (2*n+1)*(2*n+2)*sp.factorial(2*ell+2))
            A[i,ell]=sp.cancel(2*F[i,ell]+prefactor*correction)
    return F,A


def permutation_sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def polynomial_determinant(matrix,variables):
    """Determinant by its definition, using sparse exact polynomials."""
    entries=[[sp.Poly(matrix[i,j],*variables,domain=sp.ZZ)
              for j in range(matrix.cols)] for i in range(matrix.rows)]
    result=sp.Poly(0,*variables,domain=sp.ZZ)
    for perm in itertools.permutations(range(matrix.cols)):
        term=sp.Poly(permutation_sign(perm),*variables,domain=sp.ZZ)
        for i,j in enumerate(perm):
            term *= entries[i][j]
        result += term
    return result


def clear_rows(matrix,b):
    cleared=sp.zeros(matrix.rows,matrix.cols)
    row_denominators=[]
    for i in range(matrix.rows):
        denominators=[sp.fraction(sp.together(matrix[i,j]))[1] for j in range(matrix.cols)]
        common=sp.S.One
        for denominator in denominators:
            common=sp.lcm(common,denominator)
        row_denominators.append(common)
        for j in range(matrix.cols):
            cleared[i,j]=sp.cancel(common*matrix[i,j])
            assert sp.fraction(cleared[i,j])[1] == 1
    return cleared,sp.prod(row_denominators)


def source_ratio(bb):
    """Direct b-square source coefficient matrix, independent of A and P."""
    def mu(k):
        return sp.bernoulli(2*k)/sp.factorial(2*k) if k>=0 else sp.S.Zero
    def entry(t,k):
        d=2*(bb+t)+1
        e=d-8-2*bb+2*k+1
        if e<0:
            return sp.S.Zero
        coefficient=0
        for upper,lower in [(d-2*bb+1,8-2*k),(d-8+1,2*bb-2*k)]:
            if 2<=lower<=upper:
                coefficient += sp.binomial(upper,lower)/upper
        return sp.bernoulli(e)*coefficient
    M=sp.Matrix(bb,bb,entry)
    H=sp.Matrix(bb,bb,lambda i,j:mu(i+j-3))
    scalar=sp.prod(sp.factorial(2*bb+2*t-7) for t in range(bb))/sp.prod(
        sp.factorial(2*bb-2*k) for k in range(bb))
    return sp.cancel(M.det()/H.det()/scalar)


def valuation2_integer(n):
    n=abs(int(n))
    if n==0:
        raise ValueError("zero has no finite valuation")
    return (n & -n).bit_length()-1


def valuation2(q):
    numerator,denominator=sp.fraction(q)
    return valuation2_integer(numerator)-valuation2_integer(denominator)


def rational_mod(q,modulus):
    numerator,denominator=sp.fraction(q)
    denominator=int(denominator)
    assert denominator%2
    return int(numerator)*pow(denominator,-1,modulus)%modulus


def evaluate_mod(poly,values,modulus):
    total=0
    for powers,coefficient in poly.terms():
        term=int(coefficient)%modulus
        for value,power in zip(values,powers):
            term=term*pow(int(value),power,modulus)%modulus
        total=(total+term)%modulus
    return total


def run(certificate):
    b=sp.Symbol("b")
    U=sp.symbols("U1:8")
    variables=(b,*U)
    local={str(v):v for v in variables}
    P=sp.Poly(sp.sympify(certificate["numerator"],locals=local),*variables,domain=sp.ZZ)
    denominator=sp.sympify(certificate["denominator"],locals=local)
    Fdet=sp.sympify(certificate["F_determinant"],locals=local)
    F,A=rebuilt_matrices(b,U)
    print("Rebuilt both four-by-four matrices.",flush=True)
    scaled_F,Fscale=clear_rows(F,b)
    determinant_F=polynomial_determinant(scaled_F,(b,))
    fnum,fden=sp.fraction(sp.together(Fdet))
    assert determinant_F*sp.Poly(fden,b)==sp.Poly(fnum*Fscale,b)
    print("Checked the unperturbed determinant.",flush=True)
    scaled_A,Ascale=clear_rows(A,b)
    determinant_A=polynomial_determinant(scaled_A,variables)
    left=determinant_A*sp.Poly(denominator*fden,*variables)
    right=P*sp.Poly(fnum*Ascale,*variables)
    assert left == right
    print("Checked the full determinant identity coefficient by coefficient.",flush=True)

    substitution={U[j-1]:1+4*(b-j)+16*(b-j)**2 for j in range(1,8)}
    reduced=sp.Poly(P.as_expr().subs(substitution),b,domain=sp.ZZ)
    expected=16*b**2+44*b+4
    difference=reduced-sp.Poly(expected,b)
    assert all(int(c)%64==0 for c in difference.all_coeffs())
    D8=sp.cancel(denominator/(576*(2*b-5)))
    assert sp.Poly(D8,b,domain=sp.ZZ).eval(0)%2==1
    assert all(int(c)%2==0 for degree,c in sp.Poly(D8,b).terms() if degree[0]>0)
    print("Checked the universal modulo-64 reduction and odd denominator.",flush=True)

    bases={}
    for bb in range(5,11):
        value=source_ratio(bb)
        assert value==sp.Rational(certificate["finite_base_ratios"][str(bb)])
        assert value!=0
        bases[str(bb)]={"ratio":str(value),"valuation2":valuation2(value)}
    comparisons=[]
    for bb in range(8,13):
        values={b:bb,**{U[j-1]:2*sp.bernoulli(2*(bb-j)) for j in range(1,8)}}
        evaluated_P=P.eval(values)
        ratio=sp.cancel(evaluated_P/denominator.subs(b,bb))
        assert ratio==source_ratio(bb)
        comparisons.append(bb)

    bernoulli_checks=0
    for m in range(4,50):
        assert rational_mod(2*sp.bernoulli(2*m),64)==(1+4*m+16*m*m)%64
        bernoulli_checks+=1

    extrapolation=[]
    for bb in certificate["empirical_extrapolation_counterexamples"]:
        modulus=2**16
        residues=[rational_mod(2*sp.bernoulli(2*(bb-j)),modulus) for j in range(1,8)]
        P_residue=evaluate_mod(P,[bb,*residues],modulus)
        vp=valuation2_integer(P_residue)
        extrapolation.append({"b":bb,"modulus":modulus,"U_residues":residues,
                              "P_residue":P_residue,"valuation2_P":vp,
                              "valuation2_ratio":vp-6,
                              "rejected_prediction":valuation2_integer(bb-1)-4})
        assert vp-6 != valuation2_integer(bb-1)-4

    return {"all_exact_checks_passed":True,
            "determinant_method":"24 permutation products after exact row clearing",
            "integer_polynomial_monomials":len(P.terms()),
            "Bernoulli_variable_monomials":len(sp.Poly(P.as_expr(),*U).terms()),
            "determinant_identity_coefficients_checked":len(left.terms()),
            "mod64_polynomial":"16*b**2 + 44*b + 4",
            "finite_base_ratios":bases,
            "direct_source_matrix_comparisons":comparisons,
            "supplemental_Bernoulli_checks":bernoulli_checks,
            "rejected_extrapolation_examples":extrapolation,
            "rank_scope":certificate["rank_theorem"],
            "valuation_scope":certificate["valuation_theorem"],
            "source_erratum_claimed":False}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--certificate",type=Path,
                        default=Path(__file__).with_name("rank_eight_certificate.json"))
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).with_name("rank_eight_checks.json"))
    args=parser.parse_args()
    result=run(json.loads(args.certificate.read_text()))
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"passed":True,"P_monomials":result["integer_polynomial_monomials"],
                      "determinant_coefficients":result["determinant_identity_coefficients_checked"],
                      "output":str(args.output)},indent=2))


if __name__=="__main__":
    main()
