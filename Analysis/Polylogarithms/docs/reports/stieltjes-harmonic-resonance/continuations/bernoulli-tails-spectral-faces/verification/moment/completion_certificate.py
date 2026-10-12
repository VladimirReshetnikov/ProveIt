"""Portable exact certificate closing the smaller-order-ten moment conjecture.

Requirements: Python >= 3.10, SymPy.  Run from any directory; the result is
written next to this file. No source repository, network, floating arithmetic,
or precomputed multivariate determinant numerator is required.

Theorems inherited from two independently supplied reports cover all b>=6
except b=962.  Their common finite contraction A^{[5]} is reconstructed below.
At b=962, explicit row and column scalings give a matrix S integral at 2,
with det S = 2^19 mod 2^20. Hence det A != 0.
"""
from pathlib import Path
import json
import sympy as sp


def v2(q):
    q = sp.Rational(q)
    assert q != 0
    p, r = abs(int(q.p)), int(q.q)
    return (p & -p).bit_length() - (r & -r).bit_length()


def rational_mod(q, modulus):
    q = sp.Rational(q)
    assert int(q.q) % 2
    return int(q.p)*pow(int(q.q), -1, modulus) % modulus


def bernoulli_recurrence(n, modulus):
    values = [2]
    for m in range(1, n+1):
        top = 2*m+1
        choose = top*(top-1)//2
        value = 2*m-1
        for j in range(1, m):
            value = (value-choose*values[j]) % modulus
            choose = choose*(top-2*j)*(top-2*j-1)//((2*j+1)*(2*j+2))
        values.append(value*pow(top, -1, modulus) % modulus)
    return values


def falling(x, k):
    return sp.prod(x-j for j in range(k))


def contraction(a, b, variables):
    F, A = sp.zeros(a), sp.zeros(a)
    for i in range(a):
        n = b-a+i
        for ell in range(a):
            N = 2*(n-ell)+1
            R = 2*b-2*a+2+2*ell
            F[i,ell] = sp.prod((2*n-r)*(2*n+3+r)
                              for r in range(2*ell))/sp.factorial(2*ell+1)
            total = 0
            # W(N-y)=(2n+2-y)(4n+2-y)_(2i).
            for h in range(1, 2*i+2, 2):
                d = sum((-1)**(h-j)*sp.binomial(h,j)*(2*n+2-j)
                        *falling(4*n+2-j,2*i) for j in range(h+1))
                d /= sp.factorial(h)
                index = a-i+ell+(h-1)//2
                total += d*falling(N,h)*variables[index-1]
            difference = 1+4*ell-2*i
            factorial_ratio = (sp.prod(N+j for j in range(1,difference+1))
                               if difference>=0 else
                               sp.S.One/sp.prod(R+j for j in range(1,-difference+1)))
            factor = factorial_ratio/((2*n+1)*(2*n+2)*sp.factorial(2*ell+2))
            A[i,ell] = sp.expand(2*F[i,ell]+factor*total)
    return F, A


def main():
    b = 962
    output_modulus = 2**20
    input_modulus = 2**23
    variables = sp.symbols('U1:10')
    F, A = contraction(5,b,variables)
    assert not F.atoms(sp.Float) and not A.atoms(sp.Float)
    row_exponents = [1,0,6,-3,1]
    column_exponents = [0,0,-5,-4,-9]
    S = sp.diag(*[sp.Integer(2)**e for e in row_exponents])*A
    S *= sp.diag(*[sp.Integer(2)**e for e in column_exponents])
    assert sum(row_exponents)+sum(column_exponents) == -13
    # Input precision loses at most three bits under this affine map.
    coefficient_valuations = [v2(c) for entry in S
                             for c in sp.Poly(entry,*variables).coeffs() if c]
    assert min(coefficient_valuations) == -3
    bernoullis = bernoulli_recurrence(b-1,input_modulus)
    inputs = [bernoullis[b-j] for j in range(1,10)]
    exact_inputs = [2*sp.bernoulli(2*(b-j)) for j in range(1,10)]
    assert inputs == [rational_mod(q,input_modulus) for q in exact_inputs]
    S_substitute = S.subs(dict(zip(variables,inputs)))
    residue_matrix = S_substitute.applyfunc(lambda q:rational_mod(q,output_modulus))
    expected = sp.Matrix([
        [917951,442211,476112,551248,968980],
        [679904,45903,922072,654544,644616],
        [797935,540216,1028224,572168,196164],
        [491016,385277,695495,798931,823817],
        [917289,206367,412992,727792,439172],
    ])
    assert residue_matrix == expected
    determinant_residue = int(residue_matrix.det() % output_modulus)
    assert determinant_residue == 2**19
    # Independent rational evaluation of the same contraction verifies the
    # modular statement and valuation transport to the original ratio.
    S_exact = S.subs(dict(zip(variables,exact_inputs)))
    S_determinant = S_exact.det(method='domain-ge')
    assert rational_mod(S_determinant,output_modulus) == determinant_residue
    assert v2(S_determinant) == 19
    F_determinant = F.det(method='domain-ge')
    assert v2(F_determinant) == 26
    result = {
        'orders':[10,1924], 'a':5,'b':b,
        'row_exponents':row_exponents,
        'column_exponents':column_exponents,
        'input_modulus':input_modulus,
        'U_j_residues':inputs,
        'minimum_affine_coefficient_valuation':-3,
        'output_modulus':output_modulus,
        'S_residue_matrix':[[int(x) for x in residue_matrix.row(i)] for i in range(5)],
        'det_S_residue':determinant_residue,
        'valuation_det_S':19, 'valuation_det_A':32,
        'valuation_det_F':26, 'valuation_rho':6,
        'independent_exact_rational_check':True,
        'conclusion':'The remaining b=962 matrix is nonsingular.',
    }
    path = Path(__file__).with_name('completion_certificate.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
