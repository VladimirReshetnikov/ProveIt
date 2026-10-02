#!/usr/bin/env python3
"""Exact symbolic checks for the coefficient algebra in article.tex.

These checks do not certify the analytic remainders or the contour estimates.
They verify identities in rational expressions with independent phase symbols.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def main() -> None:
    alpha = sp.Symbol('alpha', positive=True)
    c, L, K = sp.symbols('c L K')
    x = sp.Symbol('x', positive=True)  # x = 1/M
    beta = sp.Rational(3, 2)
    b = {
        j: sp.simplify((-1)**(j+1) *
            (sp.bernoulli(j+1, sp.Rational(1, 2))-sp.bernoulli(j+1, 2)) /
            (j*(j+1)))
        for j in range(1, 7)
    }
    assert [b[1], b[2], b[3]] == [sp.Rational(-9, 8), sp.Rational(1, 2), sp.Rational(-21, 64)]

    # Summatory expansion: S(M)-S(M-1) must give r(M).
    s1, s2 = sp.Rational(-19, 16), sp.Rational(65, 128)
    def summatory(M, logM):
        return (alpha*M*M/2-beta*M*logM+(alpha/2+c+beta)*M
                +(b[1]-beta/2)*logM+K+s1/M+s2/M**2)
    difference = summatory(1/x, L)-summatory(1/x-1, L+sp.log(1-x))
    target = alpha/x-beta*L+c+sum(b[j]*x**j for j in range(1, 4))
    assert sp.simplify(sp.series(difference-target, x, 0, 4).removeO()) == 0

    # Psi derivatives and P_1' are independent indeterminates in this audit.
    psi1, psi2, psi_alpha, P1prime = sp.symbols('psi1 psi2 psi_alpha P1prime')
    A = (1+3*alpha)/2
    P1 = sp.Rational(27, 16)-beta*psi_alpha
    q0 = -sp.Rational(1, 2)+psi1/alpha
    q0prime = psi2/alpha
    q1 = P1prime/alpha+beta*psi1/alpha**2
    a = -(b[1]+q0)/alpha
    bb = ((sp.Rational(1, 2)-q0prime)*a-(b[2]+q1-q0*q0/2))/alpha
    U = P1+q1-b[1]-q0/2-(1+q0prime)/(2*alpha)-sp.Rational(1, 12)
    derived_D = sp.simplify(alpha*bb+(-A+psi1+q0prime)*a+U)
    stated_D = (sp.Rational(1, 6)-1/(2*alpha)-beta*psi_alpha
                +17*psi1/(8*alpha)-(psi1**2+psi2)/(2*alpha**2))
    assert sp.simplify(derived_D-stated_D) == 0
    assert sp.simplify(alpha*a+b[1]+q0) == 0
    assert not derived_D.has(P1prime)

    # The first inverse coefficient after converting from mu to log n.
    eta, C, phase0, logs = sp.symbols('eta C phase0 logs')
    v = A*A/(2*alpha**2)-(eta*logs+C+phase0)/alpha
    derived_inverse = alpha**2*v-A/2
    stated_inverse = (A*A-A)/2-alpha*eta*logs-alpha*(C+phase0)
    assert sp.simplify(derived_inverse-stated_inverse) == 0

    result = {
        'sympy_version': sp.__version__,
        'checks': [
            'First six Catalan logarithmic coefficients generated from Bernoulli polynomials',
            'S(M)-S(M-1) matches r(M) through M^(-3)',
            'The order-one saddle phase derivative cancels after reversion',
            'The stated first periodic correction D equals the exact symbolic substitution',
            "The apparent P_1 prime term cancels from D",
            'The first inverse correction agrees after conversion to log n',
        ],
        'b_coefficients': {str(j): str(value) for j, value in b.items()},
        'D_expanded': str(sp.expand(derived_D)),
        'status': 'Exact symbolic algebra; not formal verification of the analytic theorems.'
    }
    out = Path(__file__).resolve().parents[1]/'data'/'symbolic_audit.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
