#!/usr/bin/env python3
"""Exact certificates for the local normalized-radius theorem.

This program uses rational polynomial arithmetic, not numerical sampling.
The analytic reductions from parameters (a,b) to these polynomials are
proved in the article; this script checks every displayed certificate.
"""
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]


def main():
    x, y, t = s.symbols("x y t")
    U, V, W = 1+x, 1+x+y, 1+x+y+x*x
    G1 = W + U**3*s.Rational(20,27) - 2*U*V*s.Rational(5,6)
    G2 = W + U**3*s.Rational(20,27)**2 - 2*U*V*s.Rational(5,6)**2
    p6 = (800*t**6-2025*t**5+1833*t**4-567*t**3-192*t*t+233)/1458
    b6 = list(map(s.Rational, ["233/1458", "233/1458", "367/2430", "665/5832", "55/486", "95/1458", "41/729"]))
    p5 = (-5*t**5+10*t**4-11*t**3+t*t+4*t+4)/54
    b5 = list(map(s.Rational, ["2/27", "4/45", "19/180", "14/135", "1/10", "1/18"]))
    checks = {}

    def zero(name, expression):
        assert s.expand(expression) == 0, name
        checks[name] = "exact zero"

    def positive(name, value):
        assert value > 0, name
        checks[name] = str(value)

    zero("a2 substitution", G2.subs({x:t*t, y:t**3})-p6)
    zero("degree-six Bernstein expansion", p6-sum(b*s.binomial(6,j)*t**j*(1-t)**(6-j) for j,b in enumerate(b6)))
    for j,b in enumerate(b6): positive(f"degree-six Bernstein coefficient {j}", b)
    zero("a1 upper-order substitution", G1.subs({x:t*t/2, y:t**3/3})-(1-t)*p5)
    zero("degree-five Bernstein expansion", p5-sum(b*s.binomial(5,j)*t**j*(1-t)**(5-j) for j,b in enumerate(b5)))
    for j,b in enumerate(b5): positive(f"degree-five Bernstein coefficient {j}", b)
    lower_y = s.Rational(1,3)+s.Rational(22,21)*(x-s.Rational(1,2))+s.Rational(22,49)*(x-s.Rational(1,2))**2
    factored = -(2*x-1)*(10*x*x-337*x+334)/2646
    zero("subunit-inner-order factorization", G1.subs(y,lower_y)-factored)
    positive("quadratic minimum on [1/2,1]", s.Integer(10)-337+334)
    zero("quadratic derivative bound", s.diff(10*x*x-337*x+334,x)-(20*x-337))
    zero("exact corner a=b=1", G1.subs({x:s.Rational(1,2), y:s.Rational(1,3)}))
    # Alternating logarithm bounds: odd truncations bound from above,
    # even truncations from below when 0<t<1.
    log_upper = sum((-1)**(j+1)*s.Rational(7,20)**j/j for j in range(1,4))
    log_lower = s.Rational(1,5)-s.Rational(1,5)**2/2
    zero("log(27/20) upper bound", log_upper-s.Rational(7273,24000))
    zero("log(6/5) lower bound", log_lower-s.Rational(9,50))
    positive("outer-order derivative margin", s.Rational(9,8)-s.Rational(7273,6480))
    positive("log_2(3) > 11/7 certificate", s.Integer(3)**7-s.Integer(2)**11)
    positive("log_2(3) > 3/2 certificate", s.Integer(3)**2-s.Integer(2)**3)
    # Re-derive the rho^3 angular equation with arbitrary first four modes.
    rho, alpha, beta, U0, V0, W0, q3, q4, q5 = s.symbols("rho alpha beta U V W q3 q4 q5")
    delta = alpha*rho+beta*rho**3
    expr = s.sin(2*delta)-U0*q3*rho*s.cos(3*delta)-V0*q4*rho**2*s.sin(4*delta)+W0*q5*rho**3*s.cos(5*delta)
    first = s.expand(s.series(expr,rho,0,4).removeO())
    aval = U0*q3/2
    bval = s.solve(first.coeff(rho,3).subs(alpha,aval), beta)[0]
    zero("local eta coefficient from four modes", bval-aval**3/6-(U0*V0*q3*q4-W0*q5/2-U0**3*q3**3/2))
    result = {"status":"PASS", "arithmetic":"exact SymPy rational polynomial arithmetic", "sympy_version":s.__version__, "checks":checks, "count":len(checks), "bernstein_degree_six":[str(v) for v in b6], "bernstein_degree_five":[str(v) for v in b5]}
    path = ROOT/"data"/"local_radius_exact.json"
    path.write_text(json.dumps(result,indent=2)+"\n")
    print(f"PASS: {len(checks)} exact local-radius checks")


if __name__ == "__main__": main()
