#!/usr/bin/env python3
"""Independent exact checker: Python standard library only.

Checks coefficient positivity AND the claimed polynomial identities on a
provably sufficient interpolation grid. This is not a numerical sample test:
explicit degree bounds make the finite exact grids identity certificates.
Also checks ratio-barrier induction at n=5, all initial minors, and D_6(1)<0.
Run: python code/verify_certificates.py
"""
from __future__ import annotations
import json
import sys
from fractions import Fraction as Q
from math import comb, prod
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_NEGATIVE = -26875777009408537346562624


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def determinant(matrix: list[list[Q]]) -> Q:
    """Exact Gaussian elimination, with pivoting; no floating point."""
    a = [[Q(v) for v in row] for row in matrix]
    size = len(a)
    result = Q(1)
    for k in range(size):
        pivot = next((i for i in range(k,size) if a[i][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        v = a[k][k]
        result *= v
        for i in range(k+1,size):
            multiplier = a[i][k]/v
            for j in range(k+1,size):
                a[i][j] -= multiplier*a[k][j]
    return result


def sequence(last: int) -> list[int]:
    c = [1,2]
    for n in range(1,last):
        numerator = (26*n*n+13*n+2)*c[n] + (27*n*n-27*n+6)*c[n-1]
        value, remainder = divmod(numerator,(n+1)**2)
        require(remainder == 0, f"nonintegral recurrence at {n}")
        c.append(value)
    return c[:last+1]


def poly_value(record: dict, n: int) -> Q:
    z = n-record["shift"]
    value = 0
    for coefficient in reversed(record["coefficients"]):
        value = value*z+int(coefficient)
    return Q(record["scale"])*value


def main() -> None:
    started = perf_counter()
    data = json.loads((ROOT/"data"/"certificates.json").read_text(encoding="utf-8"))
    require(data["format"] == "A279619-Hankel-exact-certificates-v1", "wrong format")
    expected_b = [
        Q(27), -Q(81,2), Q(6315,112), -Q(56445,784), Q(30827295,351232),
        -Q(508917075,4917248), Q(65617849635,550731776),
        -Q(1040841454725,7710244864), Q(520118139886395,3454189699072),
        -Q(8041730705126175,48358655787008),
        Q(988630328840718285,5416169448144896)]
    b = [Q(v) for v in data["ratio_coefficients"]]
    require(b[:11] == expected_b,"ratio polynomial does not match the article")
    K = Q(14943122191587178247,37913186137014272)
    require(Q(data["K"]) == K,"incorrect barrier width")
    expected_exponents = {2:[2],3:[6,4,2],4:[8,8,6,4,2],5:[10,10,10,8,6,4,2]}
    polys = data["polynomials"]
    expected_names = {"ell","induction_lower","induction_upper"}
    expected_names |= {f"H{r}_B{k}" for r in range(2,6) for k in range(r+1)}
    require(set(polys) == expected_names,"missing or extra polynomial")
    count = 0
    for name,record in polys.items():
        require(record["shift"] == 5,"wrong shift")
        require(Q(record["scale"]) > 0,f"nonpositive scale: {name}")
        require(record["degree"]+1 == len(record["coefficients"]),"degree mismatch")
        require(all(int(v)>0 for v in record["coefficients"]),f"coefficient sign: {name}")
        count += len(record["coefficients"])
    require(count == 1090,"wrong coefficient count")
    print("PASS: 21 polynomials; 1,090 strictly positive rational coefficients.",flush=True)

    def ell(n: int) -> Q:
        return sum((b[j]*n**(11-j) for j in range(11)),Q(0))-K
    def h(n: int) -> Q:
        return ell(n)+2*K
    p = lambda n:26*n*n+13*n+2
    q = lambda n:27*n*n-27*n+6
    # Degrees: ell <= 11; both cross-multiplied induction expressions <= 24.
    require(polys["ell"]["degree"] <= 11,"ell degree")
    for n in range(5,17):
        require(poly_value(polys["ell"],n) == ell(n),"ell identity")
    for name in ("induction_lower","induction_upper"):
        require(polys[name]["degree"] <= 24,"induction degree")
    for n in range(5,30):
        lower = (p(n+1)*h(n)+q(n+1)*n**11)*(n+1)**11-(n+2)**2*h(n)*ell(n+1)
        upper = (n+2)**2*ell(n)*h(n+1)-(p(n+1)*ell(n)+q(n+1)*n**11)*(n+1)**11
        require(poly_value(polys["induction_lower"],n) == lower,"lower identity")
        require(poly_value(polys["induction_upper"],n) == upper,"upper identity")
    c = sequence(30)
    require(ell(5)/5**11 < Q(c[6],c[5]) < h(5)/5**11,"barrier base n=5")
    print("PASS: exact ratio-barrier identities and base case; induction covers n>=5.",flush=True)

    points = 0
    for r in range(2,6):
        exponents = expected_exponents[r]
        require(data["determinant_denominator_exponents"][str(r)] == exponents,
                "wrong determinant denominator")
        m = 2*r-2
        d_degree = 2*(m-1)
        bound = r*(11+d_degree)  # = 4r^2+5r
        multiplier_degree = r*d_degree-sum(exponents)
        for k in range(r+1):
            require(polys[f"H{r}_B{k}"]["degree"]+multiplier_degree <= bound,
                    "insufficient interpolation degree bound")
        # Both sides are polynomials of n-degree <= bound and u-degree <= r.
        # (bound+1)*(r+1) distinct exact evaluation points prove equality.
        for n in range(5,5+bound+1):
            den = prod((n+j)**2 for j in range(2,m+1))
            E = prod((n+j)**exponent for j,exponent in enumerate(exponents,2))
            multiplier,remainder = divmod(den**r,E)
            require(remainder==0,"denominator quotient is not polynomial")
            bernstein = [poly_value(polys[f"H{r}_B{k}"],n) for k in range(r+1)]
            for v in range(r+1):
                u = Q(v,r)
                R = (ell(n)+2*K*u)/n**11
                x = [Q(1),R]
                for k in range(1,m):
                    x.append((p(n+k)*x[k]+q(n+k)*x[k-1])/(n+k+1)**2)
                lhs = determinant([[n**11*den*x[i+j] for j in range(r)] for i in range(r)])
                rhs = multiplier*sum((bernstein[k]*comb(r,k)*u**k*(1-u)**(r-k)
                                      for k in range(r+1)),Q(0))
                require(lhs==rhs,f"H{r} polynomial identity failed at n={n},u={u}")
                points += 1
        for n in range(5):
            value = determinant([[Q(c[n+i+j]) for j in range(r)] for i in range(r)])
            require(value>0,f"initial H{r}({n}) not positive")
        print(f"PASS: all H{r}(n)>0, using a degree-{bound} identity grid and n=0..4.",flush=True)
    negative = determinant([[Q(c[1+i+j]) for j in range(6)] for i in range(6)])
    require(negative==EXPECTED_NEGATIVE,"incorrect order-six obstruction")
    print(f"PASS: D_6(1) = {negative}.")
    moment = json.loads((ROOT/"data"/"moment_obstruction.json").read_text())
    qp = [int(v) for v in moment["integer_polynomial_coefficients_increasing"]]
    require(len(qp)==6 and qp[-1]==6107572673541,"wrong obstruction polynomial")
    for j in range(5):
        require(sum(qp[i]*c[i+j+1] for i in range(6))==0,"moment orthogonality")
    bad = sum(qp[i]*qp[j]*c[i+j+1] for i in range(6) for j in range(6))
    require(bad==int(moment["negative_functional_value"])<0,"negative quadratic form")
    repair = -Q(bad,qp[-1]**2)
    require(repair==Q(moment["minimal_repair"]),"moment repair")
    require(Q(c[11])+repair==Q(moment["minimal_c11"]),"minimum twelfth moment")
    require(determinant([[Q(c[i+j]) for j in range(6)] for i in range(6)])>0,
            "unshifted six by six matrix must be positive definite")
    print("PASS: twelfth-moment obstruction, orthogonality, and exact minimal repair.")
    print(f"PASS: {points} exact bivariate interpolation points; no floating point used.")
    print("VERIFIED: the supplied certificates prove contiguous positivity through order 5.")
    print("Classical Fekete reduction gives TP_5; the negative minor excludes TN_6.")
    print(f"Elapsed seconds (informational only): {perf_counter()-started:.3f}")

if __name__ == "__main__":
    try:
        main()
    except (ArithmeticError,ValueError,KeyError,OSError) as error:
        print(f"VERIFICATION FAILED: {error}",file=sys.stderr)
        raise SystemExit(1)
