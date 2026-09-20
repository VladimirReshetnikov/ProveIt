#!/usr/bin/env python3
"""Optional discovery script: derive the spectral and generating-function data.

Requires SymPy.  This is NOT needed by verify.py.  Output goes to stdout and
optionally --output FILE; the distributed certificates are not overwritten.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

from tribonacci import LABELS, load_automaton


def derive() -> dict:
    import sympy as s
    from sympy.polys.matrices import DomainMatrix
    data = load_automaton()
    transitions, outputs = data['transitions'], data['outputs']
    n = len(transitions)
    A = s.zeros(n)
    for q, row in enumerate(transitions):
        for t in row:
            if t >= 0:
                A[q, t] += 1
    x, z = s.symbols('x z')
    characteristic = A.charpoly(x).as_expr()
    # The multiplication rule beta*(a+b beta+c beta^2)=(c)+(a+c) beta+(b+c) beta^2
    # turns an algebraic eigenvector computation into a rational linear system.
    equations = s.zeros(3*n+3, 3*n+1)
    for j in range(n):
        for i in range(n):
            if A[i,j]:
                for k in range(3):
                    equations[3*j+k,3*i+k] += A[i,j]
        equations[3*j,3*j+2] -= 1
        equations[3*j+1,3*j] -= 1
        equations[3*j+1,3*j+2] -= 1
        equations[3*j+2,3*j+1] -= 1
        equations[3*j+2,3*j+2] -= 1
    for i in range(n):
        for k in range(3):
            equations[3*n+k,3*i+k] = 1
    equations[3*n,3*n] = 1
    reduced, pivots = DomainMatrix.from_Matrix(equations).to_field().rref()
    reduced = reduced.to_Matrix()
    if len(pivots) != 3*n:
        raise ValueError('The normalized algebraic eigenvector is not unique')
    solution = [reduced[i,3*n] for i in range(3*n)]
    denominator = s.ilcm(*(entry.q for entry in solution))
    eigenvector = [[int(denominator*solution[3*i+j]) for j in range(3)] for i in range(n)]

    v = [0]*n
    v[0] = 1
    sequences = {label: [] for label in LABELS}
    for k in range(n+1):
        for label in LABELS:
            sequences[label].append(sum(v[q] for q in range(n) if outputs[q] == label))
        following = [0]*n
        for q, row in enumerate(transitions):
            for t in row:
                if t >= 0:
                    following[t] += v[q]
        v = following
    denominator_all = s.expand(z**n*characteristic.subs(x,1/z))
    functions = {}
    gf_data = {}
    for label, sequence in sequences.items():
        convolution = s.Poly(denominator_all*sum(a*z**i for i,a in enumerate(sequence)),z)
        numerator = sum(convolution.nth(i)*z**i for i in range(n))
        rational_function = s.cancel(numerator/denominator_all)
        numerator, denominator_reduced = map(lambda p:s.Poly(p,z),
                                             s.fraction(rational_function))
        constant = denominator_reduced.nth(0)
        numerator = s.Poly(numerator.as_expr()/constant,z)
        denominator_reduced = s.Poly(denominator_reduced.as_expr()/constant,z)
        gf_data[str(label)] = {
            'numerator': [int(numerator.nth(i)) for i in range(numerator.degree()+1)],
            'denominator': [int(denominator_reduced.nth(i))
                            for i in range(denominator_reduced.degree()+1)],
            'coefficient_order': 'ascending powers of z',
        }
        functions[str(label)] = str(s.factor(rational_function))
    return {'sympy_version':s.__version__, 'characteristic_polynomial_factored':str(s.factor(characteristic)),
            'eigenvector_denominator':int(denominator), 'eigenvector_coefficients':eigenvector,
            'generating_functions_factored':functions, 'generating_function_coefficients':gf_data}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    try:
        result = derive()
        text = json.dumps(result,indent=2)+'\n'
        if args.output:
            args.output.write_text(text,encoding='utf-8')
        print(text)
    except ImportError:
        parser.exit(2,'This optional derivation requires SymPy; verify.py does not.\n')


if __name__ == '__main__':
    main()
