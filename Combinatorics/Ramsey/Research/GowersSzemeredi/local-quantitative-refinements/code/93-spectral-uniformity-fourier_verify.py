#!/usr/bin/env python3
"""Exact algebra and independent primal/dual checks for the Fourier results.

The polynomial identities use rational arithmetic, without a computer
algebra package. Numerical sampling supplements the written global proofs;
it is not used as a proof of positivity on an interval.

Dependencies for numerical checks: NumPy, SciPy.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, linprog
from numpy.polynomial.chebyshev import chebval, chebvander


class Poly:
    """A small sparse exact polynomial ring Q[c,b,x,u,v]."""

    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            self.terms = terms.terms.copy()
        elif isinstance(terms, dict):
            self.terms = {k: Fraction(a) for k, a in terms.items() if a}
        else:
            self.terms = {(0, 0, 0, 0, 0): Fraction(terms)} if terms else {}

    @classmethod
    def variable(cls, i):
        powers = [0, 0, 0, 0, 0]
        powers[i] = 1
        return cls({tuple(powers): 1})

    def __add__(self, other):
        other = Poly(other)
        ans = self.terms.copy()
        for powers, value in other.terms.items():
            ans[powers] = ans.get(powers, 0) + value
        return Poly(ans)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -a for k, a in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly(other))

    def __rsub__(self, other):
        return Poly(other) - self

    def __mul__(self, other):
        other = Poly(other)
        ans = {}
        for p, a in self.terms.items():
            for q, b in other.terms.items():
                r = tuple(i + j for i, j in zip(p, q))
                ans[r] = ans.get(r, 0) + a * b
        return Poly(ans)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only nonnegative integer polynomial powers")
        ans, base = Poly(1), self
        while n:
            if n & 1:
                ans = ans * base
            base = base * base
            n //= 2
        return ans

    def __truediv__(self, scalar):
        return self * (1 / Fraction(scalar))

    def __eq__(self, other):
        return self.terms == Poly(other).terms


class Rat:
    """Rational functions, compared by exact cross multiplication."""

    def __init__(self, numerator=0, denominator=1):
        if isinstance(numerator, Rat):
            self.n, self.d = numerator.n, numerator.d
        else:
            self.n, self.d = Poly(numerator), Poly(denominator)

    def __add__(self, other):
        other = Rat(other)
        return Rat(self.n * other.d + other.n * self.d, self.d * other.d)

    __radd__ = __add__

    def __neg__(self):
        return Rat(-self.n, self.d)

    def __sub__(self, other):
        return self + (-Rat(other))

    def __rsub__(self, other):
        return Rat(other) - self

    def __mul__(self, other):
        other = Rat(other)
        return Rat(self.n * other.n, self.d * other.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Rat(other)
        return Rat(self.n * other.d, self.d * other.n)

    def __rtruediv__(self, other):
        return Rat(other) / self

    def __pow__(self, n):
        return Rat(self.n**n, self.d**n)

    def __eq__(self, other):
        other = Rat(other)
        return self.n * other.d == other.n * self.d


def chebyshev(j, x):
    if j == 0:
        return x * 0 + 1
    t0, t1 = x * 0 + 1, x
    for _ in range(1, j):
        t0, t1 = t1, 2 * x * t1 - t0
    return t1


def exact_checks():
    passed = []

    def check(name, left, right):
        assert left == right, name
        passed.append(name)

    c, v, x = (Poly.variable(j) for j in range(3))
    d = lambda z: (1 - z) * (2 * z + 1)
    n = lambda z: z**2 * (4 * z**2 - 3)
    h_poly = (
        4 * d(c) * v**3
        + 4 * c * d(c) * v**2
        + (c + 1) * (4 * c**2 - 3) * v
        + c * (4 * c**2 - 3)
    )
    check("contact equation cubic factor", n(v) * d(c) - n(c) * d(v),
          (v - c) * h_poly)
    transition = 12*c**4 + 6*c**3 - 11*c**2 - 5*c + 1
    check("transition polynomial under y=2c",
          3*(2*c)**4+3*(2*c)**3-11*(2*c)**2-10*(2*c)+4,
          4*transition)
    check(
        "quartic transition factorization",
        c**2 * (4*c**2 - 3) * (1+2*c) * (2+3*c)
        + (1-c) * (1+c)**2 * (1-4*c-8*c**2),
        (2*c**2 + 2*c + 1) * transition,
    )
    check("contact existence lower bound factor",
          2*n(c) + d(c), (c+1)*(2*c-1)*(4*c**2-2*c-1))

    s, p = v+c, v*c
    h_symmetric = 4*s**3 + 4*p*s**2 - 8*p**2*s - 8*p*s - 4*p**2 - 3*s - 3*p
    check("symmetric contact equation", h_poly, h_symmetric)
    j_poly = (1+2*p)**2 - 2*s*(s+p)
    check("upper unused-moment identity", h_poly,
          -s-2*s*j_poly-4*p**2-3*p)
    r_num, r_den = 1+2*p, 1-2*s
    check("lower unused-moment factorization",
          2*s*(r_den-r_num) + r_num*(4*p+4),
          4*(1-v)*(1-c)*(1+v+c+2*v*c))
    check("upper unused-moment expansion",
          2*s*(r_den-r_num) + r_num*(4*p+2), 2*j_poly)

    hh = 3*v**2 + 2*v*c + c**2
    q0 = Poly(Fraction(3, 8)) - hh/2 - v**2*c*(2*v+c)
    q1 = 2*v*(v+c)**2
    q2 = (1-hh)/2
    q4 = Fraction(1, 8)
    k = -q1-q2+q4
    check("central quartic Chebyshev expansion",
          (x-v)**2*(x-c)*(x+2*v+c),
          q0+q1*chebyshev(1,x)+q2*chebyshev(2,x)+q4*chebyshev(4,x))
    check("central primal dual value identity",
          q0*r_den+k*r_num, h_poly/4)

    uu, vv = Poly.variable(3), Poly.variable(4)
    ss, pp = uu+vv, uu*vv
    aa = pp-ss**2-c*ss-c**2
    grid_q0 = Poly(Fraction(3,8))+aa/2-pp*c*(ss+c)
    grid_q1 = ss*(uu+c)*(vv+c)
    grid_q2 = (1+aa)/2
    grid_k = -grid_q1-grid_q2+Fraction(1,8)
    check("discrete quartic Chebyshev expansion",
          (x-uu)*(x-vv)*(x-c)*(x+ss+c),
          grid_q0+grid_q1*chebyshev(1,x)+grid_q2*chebyshev(2,x)
          +Fraction(1,8)*chebyshev(4,x))
    check("exact grid error identity modulo contact cubic",
          grid_q0*r_den+grid_k*r_num+d(c)*(v-uu)*(v-vv)*(v+uu+vv+c),
          h_poly/4)

    f3_num, f3_den = 1-2*c**2, 3+2*c-4*c**2
    m4_plus_num = (
        f3_num*(-20*c**2+6*c+13)
        +(4*c**2-2*c-3)*f3_den
    )
    check("inherited fourth moment lower endpoint",
          m4_plus_num, 2*(c-1)*(3*c+2)*(4*c**2+2*c-1))
    check("inherited fourth moment upper endpoint",
          m4_plus_num-2*f3_num*(2*c+1), 2*transition)

    cc = Rat(c)
    vv = -1/(4*cc)
    f4_den = 3+10*cc-12*cc**2
    rr = (1+2*cc-4*cc**2)/f4_den
    wm = ((1-cc)*(4*cc+1)*(4*cc**2+2*cc-1)
          /(f4_den*(4*cc-1)*(cc+1)))
    wv = 128*cc**4*(1-cc)/(f4_den*(4*cc-1)*(4*cc**2+1))
    wc = 2*(4*cc+1)/(f4_den*(cc+1)*(4*cc**2+1))
    check("first cutoff-four masses sum to one", wm+wv+wc, Rat(1))
    for j in range(1, 5):
        check(f"first cutoff-four moment {j}",
              ((-1)**j)*wm+wv*chebyshev(j,vv)+wc*chebyshev(j,cc), -rr)

    vv3 = -(cc+1)/(2*cc+1)
    rr3 = (1-2*cc**2)/(3+2*cc-4*cc**2)
    wc3 = (-rr3-vv3)/(cc-vv3)
    for j in range(1, 4):
        check(f"first cutoff-three moment {j}",
              wc3*chebyshev(j,cc)+(1-wc3)*chebyshev(j,vv3), -rr3)

    mod5_values = [(y**4+y**3+3*y*y+3) % 5 for y in range(5)]
    assert mod5_values == [3,3,4,3,1]
    assert all(mod5_values)
    passed.append("transition mod-five polynomial has no linear factor")
    quadratic_rows = []
    for beta in range(1,5):
        for delta in range(1,5):
            if beta*delta % 5 != 3:
                continue
            pairs = [(alpha,gamma) for alpha in range(5) for gamma in range(5)
                     if (alpha+gamma) % 5 == 1
                     and (alpha*delta+beta*gamma) % 5 == 0]
            assert len(pairs) == 1
            alpha,gamma = pairs[0]
            middle = (alpha*gamma+beta+delta) % 5
            assert middle != 3
            quadratic_rows.append([beta,delta,alpha,gamma,middle])
    assert quadratic_rows == [[1,3,2,4,2],[2,4,4,2,4],
                              [3,1,4,2,2],[4,2,2,4,4]]
    passed.append("transition mod-five polynomial has no quadratic factor")

    with localcontext() as ctx:
        ctx.prec = 80
        cd = Decimal("0.15")
        for _ in range(12):
            aa = 12*cd**4+6*cd**3-11*cd**2-5*cd+1
            ad = 48*cd**3+18*cd**2-22*cd-5
            cd -= aa/ad
        transition_decimal = str(cd)
    return {"identities_passed": len(passed), "identities": passed,
            "transition_c_80_digit_Newton": transition_decimal,
            "transition_mod5_values":mod5_values,
            "transition_mod5_quadratic_rows":quadratic_rows}


C_MINUS = (1-math.sqrt(5))/4
C_ZERO = (math.sqrt(5)-1)/4
C_STAR = brentq(lambda c: 12*c**4+6*c**3-11*c*c-5*c+1, 0, .2,
                xtol=5e-16)
A_STAR = math.acos(C_STAR)


def contact_node(c):
    """The unique cosine root on [-1,-sqrt(3)/2]."""
    def hh(x):
        return x*x*(4*x*x-3)/((1-x)*(2*x+1))

    target = hh(c)
    right = -math.sqrt(3)/2
    if target <= -.5 + 1e-14:
        return -1.
    if target >= -1e-15:
        return right
    return brentq(lambda v: hh(v)-target, -1., right, xtol=5e-16)


def allr_solution(r_cutoff, a):
    b = math.pi-a
    c = math.cos(a)
    coeff = np.zeros(r_cutoff+1)
    if b <= math.pi/(r_cutoff+1) + 1e-15:
        coeff[1] = -1.
        return {"rho": -c, "nodes": np.array([c]),
                "weights": np.array([1.]), "dual": coeff,
                "branch": "pure endpoints", "active_index": 1}
    assert b <= 2*math.pi/(r_cutoff+1) + 1e-13
    r = min(r_cutoff, math.floor(math.pi/b+.5))
    z, w = math.cos(b), math.cos(r*b)
    den = 2-z-w
    rho, pp = (z-w)/den, 2/den
    uu = (1-w)/den
    coeff[1] = -uu
    coeff[r] = (-1)**(r+1)*(1-uu)
    return {"rho": rho, "nodes": np.array([-1., c]),
            "weights": np.array([1-pp, pp]), "dual": coeff,
            "branch": "three angular atoms", "active_index": r}


def phi4_solution(a):
    """Value, cosine extremizer, and normalized nonconstant dual."""
    c = math.cos(a)
    if a < math.pi/5-1e-14:
        return {"rho": 0.,
                "nodes": np.cos((2*np.arange(5)+1)*math.pi/5),
                "weights": np.ones(5)/5, "dual": np.zeros(5),
                "branch": "zero"}
    if a <= 2*math.pi/5+1e-14:
        v = -1/(4*c)
        den = 3+10*c-12*c*c
        rho = (1+2*c-4*c*c)/den
        wm = ((1-c)*(4*c+1)*(4*c*c+2*c-1)
              /(den*(4*c-1)*(c+1)))
        wv = 128*c**4*(1-c)/(den*(4*c-1)*(4*c*c+1))
        wc = 2*(4*c+1)/(den*(c+1)*(4*c*c+1))
        q = np.array([
            -.375+(c-2*v*(c-1)-v*v)/2+c*v*v,
            (c-1)*(.75+v*v)+v*(1.5-2*c),
            ((c-1)*(1-2*v)-v*v)/2,
            (c-1+2*v)/4,
            -.125,
        ])
        k = -q[1:].sum()
        dual = q/k
        dual[0] = 0.
        return {"rho": rho, "nodes": np.array([-1.,v,c]),
                "weights": np.array([wm,wv,wc]), "dual": dual,
                "branch": "first four"}
    if a <= A_STAR+1e-14:
        v = -(c+1)/(2*c+1)
        rho = (1-2*c*c)/(3+2*c-4*c*c)
        pp = (-rho-v)/(c-v)
        q = np.array([(c+2*v)/2+c*v*v,
                      -.75-2*c*v-v*v, (c+2*v)/2, -.25, 0.])
        k = -q[1:].sum()
        dual = q/k
        dual[0] = 0.
        return {"rho": rho, "nodes": np.array([v,c]),
                "weights": np.array([1-pp,pp]), "dual": dual,
                "branch": "inherited three"}
    if a <= 3*math.pi/5+1e-14:
        v = contact_node(c)
        dd = lambda t: (1-t)*(2*t+1)
        pp = -dd(v)/(dd(c)-dd(v))
        rho = (1+2*c*v)/(1-2*c-2*v)
        hh = 3*v*v+2*v*c+c*c
        q = np.array([.375-hh/2-v*v*c*(2*v+c),
                      2*v*(v+c)**2, (1-hh)/2, 0., .125])
        k = -q[1]-q[2]+q[4]
        dual = q/k
        dual[0] = 0.
        return {"rho": rho, "nodes": np.array([v,c]),
                "weights": np.array([1-pp,pp]), "dual": dual,
                "branch": "new central"}
    return allr_solution(4,a)


def numerical_checks(samples=2001, max_cutoff=64):
    checks = {
        "phi4_samples": 0,
        "all_R_samples": 0,
        "max_mass_sum_error": 0.,
        "min_mass": 1.,
        "max_primal_value_error": 0.,
        "max_dual_norm_error": 0.,
        "min_sampled_dual_gap": 0.,
        "max_dual_contact_error": 0.,
        "branches_seen": [],
    }
    branches = set()

    def inspect(r_cutoff, a, solution):
        rho = solution["rho"]
        nodes, weights, dual = (solution[k] for k in ("nodes","weights","dual"))
        moments = chebvander(nodes,r_cutoff).T @ weights
        objective = np.max(np.abs(moments[1:]))
        checks["max_mass_sum_error"] = max(checks["max_mass_sum_error"],
                                            abs(weights.sum()-1))
        checks["min_mass"] = min(checks["min_mass"],float(weights.min()))
        checks["max_primal_value_error"] = max(checks["max_primal_value_error"],
                                                abs(float(objective)-rho))
        if solution["branch"] == "zero":
            return
        checks["max_dual_norm_error"] = max(checks["max_dual_norm_error"],
                                              abs(abs(dual[1:]).sum()-1))
        checks["max_dual_contact_error"] = max(checks["max_dual_contact_error"],
                                                float(np.max(abs(chebval(nodes,dual)-rho))))
        theta = np.linspace(a,math.pi,257)
        gap = chebval(np.cos(theta),dual)-rho
        checks["min_sampled_dual_gap"] = min(checks["min_sampled_dual_gap"],
                                               float(gap.min()))
        assert nodes.max() <= math.cos(a)+2e-12

    angles = list(np.linspace(.0001,math.pi,samples))
    angles += [math.pi/5,2*math.pi/5,A_STAR,math.pi/2,
               3*math.pi/5,5*math.pi/7,4*math.pi/5,math.pi]
    for a in angles:
        sol = phi4_solution(a)
        inspect(4,a,sol)
        branches.add(sol["branch"])
        checks["phi4_samples"] += 1
    for r_cutoff in range(2,max_cutoff+1):
        for b in np.linspace(0,2*math.pi/(r_cutoff+1),129):
            a = math.pi-float(b)
            inspect(r_cutoff,a,allr_solution(r_cutoff,a))
            checks["all_R_samples"] += 1

    checks["branches_seen"] = sorted(branches)
    assert checks["min_mass"] >= -2e-10
    assert checks["max_mass_sum_error"] <= 2e-10
    assert checks["max_primal_value_error"] <= 2e-10
    assert checks["max_dual_norm_error"] <= 2e-10
    assert checks["min_sampled_dual_gap"] >= -2e-10
    assert checks["max_dual_contact_error"] <= 2e-10
    checks["numerical_tolerance"] = 2e-10
    return checks


def grid_solution(n, first_index):
    """The three-node finite certificate, with its explicit hypotheses checked."""
    a = 2*math.pi*first_index/n
    c = math.cos(a)
    assert C_MINUS < c < C_STAR
    b = contact_node(c)
    continuous = phi4_solution(a)
    rho = continuous["rho"]
    wb = continuous["weights"][0]
    xs = np.cos(2*math.pi*np.arange(first_index,n//2+1)/n)[::-1]
    closest = int(np.argmin(abs(xs-b)))
    if abs(xs[closest]-b) <= 2e-13:
        return {"rho":rho, "xs":xs, "nodes":np.array([xs[closest],c]),
                "weights":continuous["weights"], "exact_error":0.,
                "error_prediction":0., "exact_contact":True}
    u = float(xs[xs < b].max())
    v = float(xs[xs > b].min())
    dd = lambda x: 2*x*x-x-1
    ee = lambda x: 8*x**4-8*x*x+x+1
    ff = lambda x: ee(x)-ee(c)*dd(x)/dd(c)
    eu, ev = -ff(v), ff(u)
    ec = -(eu*dd(u)+ev*dd(v))/dd(c)
    weights = np.array([eu,ev,ec])/(eu+ev+ec)
    ss, pp = u+v, u*v
    aa = pp-ss*ss-c*ss-c*c
    q0 = .375+aa/2-pp*c*(ss+c)
    q1 = ss*(u+c)*(v+c)
    q2 = (1+aa)/2
    kk = -q1-q2+.125
    rho_n = -q0/kk
    nodes = np.array([u,v,c])
    moments = chebvander(nodes,4).T @ weights
    assert u < b < v < c
    assert u < -.5 and v < -.5
    assert ss+2*c < 0 and q1 < 0 and q2 < 0 and rho_n > 0
    assert abs(moments[3]) <= rho_n+2e-11
    assert np.max(abs(moments[1:])) <= rho_n+2e-11
    assert np.min(weights) >= -2e-11
    prediction = wb*(b-u)*(v-b)*(b-c)*(b+ss+c)/kk
    return {"rho":rho_n, "xs":xs, "nodes":nodes, "weights":weights,
            "exact_error":rho_n-rho, "error_prediction":prediction,
            "exact_contact":False}


def grid_checks():
    summary = {"grid_certificates":0, "independent_LP_comparisons":0,
               "exact_continuous_contacts":0, "max_LP_difference":0.,
               "max_exact_error_identity_residual":0.,
               "half_circle_N_values":[], "asymptotic_samples":[]}
    cases = set()
    for n in (64,65,96,127,128,256,511):
        for c in np.linspace(-.25,.12,9):
            first = math.ceil(n*math.acos(float(c))/(2*math.pi))
            cases.add((n,first))
    for n in range(8,513,4):
        cases.add((n,n//4))
        summary["half_circle_N_values"].append(n)

    for n,first in sorted(cases):
        sol = grid_solution(n,first)
        summary["grid_certificates"] += 1
        summary["exact_continuous_contacts"] += int(sol["exact_contact"])
        summary["max_exact_error_identity_residual"] = max(
            summary["max_exact_error_identity_residual"],
            abs(sol["exact_error"]-sol["error_prediction"]))
        xs = sol["xs"]
        moments = chebvander(xs,4)[:,1:].T
        aa = np.concatenate([
            np.column_stack([moments,-np.ones(4)]),
            np.column_stack([-moments,-np.ones(4)])])
        lp = linprog(
            np.r_[np.zeros(len(xs)),1.], A_ub=aa,b_ub=np.zeros(8),
            A_eq=np.r_[np.ones(len(xs)),0.][None,:],b_eq=[1.],
            bounds=(0,None),method="highs",
            options={"primal_feasibility_tolerance":1e-9,
                     "dual_feasibility_tolerance":1e-9})
        assert lp.success, (n,first,lp.message)
        summary["independent_LP_comparisons"] += 1
        summary["max_LP_difference"] = max(summary["max_LP_difference"],
                                           abs(float(lp.fun)-sol["rho"]))

    limiting_coefficient = 2*math.pi**2*(2*math.sqrt(3)-3)/9
    for n in (256,512,1024,2048,4096,8192):
        sol = grid_solution(n,n//4)
        # Use the exact error identity to avoid cancellation in rho_N-rho.
        scaled_error = n*n*sol["error_prediction"]
        summary["asymptotic_samples"].append({
            "N":n,"N_mod_12":n%12,"N_squared_error":scaled_error,
            "predicted_limit":limiting_coefficient})
    assert summary["max_LP_difference"] < 2e-8
    assert summary["max_exact_error_identity_residual"] < 2e-11
    summary["LP_tolerance"] = 2e-8
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).with_name("fourier_verification_results.json"))
    parser.add_argument("--samples",type=int,default=2001)
    parser.add_argument("--max-cutoff",type=int,default=64)
    args = parser.parse_args()
    results = {"exact":exact_checks(),
               "numerical":numerical_checks(args.samples,args.max_cutoff),
               "finite_grid":grid_checks(),
               "status":"all checks passed",
               "scope":"exact algebra plus sampled diagnostics; written positivity proofs are separate"}
    args.output.write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
