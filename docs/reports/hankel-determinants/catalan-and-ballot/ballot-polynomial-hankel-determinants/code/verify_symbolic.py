"""Optional SymPy checks and exact numerator data.

Run after installing requirements.txt:
    python code/verify_symbolic.py
The independent symbolic determinants use both u and t. The GF tests use
sparse integer polynomial arithmetic, keeping every parameter symbolic.
"""
import csv
import json
import time
from collections import defaultdict
from math import comb
from pathlib import Path

import sympy as sp
from hankel import admissible, coefficient, delta_polynomial, rho_coefficients, sign_power


def main() -> None:
    started = time.perf_counter()
    t,u = sp.symbols("t u")
    determinant_checks = 0
    for k in range(1,7):
        for n in range(1,5):
            def moment(m):
                return sum((comb(m,h)-(comb(m,h-1) if h else 0))
                           *u**(m-2*h)*t**h for h in range(m//2+1))
            direct = sp.det(sp.Matrix(n,n,lambda i,j: moment(k+i+j)))
            formula = (t**(n*(n-1)//2)*sign_power(k*n*(n-1)//2)
                       *sum(coefficient(k,n,a)*u**a*t**((k*n-a)//2)
                            for a in admissible(k,n)))
            if sp.expand(direct-formula) != 0:
                raise AssertionError((k,n))
            determinant_checks += 1
    records = []
    gf_tail_checks = 0
    reciprocity_checks = 0
    for k in range(1,11):
        r = k//2
        # Denominator triples are (degree in x, degree in t, integer coefficient).
        terms = []
        if k%2:
            power = r*r+r+1
            for j in range(power+1):
                terms.append((2*j,k*j,comb(power,j)))
        else:
            power = r*r
            for j in range(power+1):
                c = sign_power(j)*comb(power,j)
                terms += [(2*j,2*r*j,c),(2*j+1,2*r*j+r,-c)]
        D = max(a for a,b,c in terms)
        degree = D-k
        seq = [delta_polynomial(k,n) for n in range(D+9)]
        A = {}
        for n in range(D+9):
            result = defaultdict(int)
            for dx,dt,c in terms:
                if dx<=n:
                    for j,v in enumerate(seq[n-dx]):
                        if v:
                            result[j+dt] += c*v
            result = {j:v for j,v in result.items() if v}
            if n>degree:
                if result:
                    raise AssertionError(("GF tail",k,n,result))
                gf_tail_checks += 1
            else:
                for j,v in result.items():
                    A[(n,j)] = v
        if max(i for i,j in A) != degree:
            raise AssertionError(("Degree",k))
        T = 2*r*r*(r-1) if k%2==0 else k*r*r
        sign = 1 if k%2==0 else sign_power(r)
        transformed = {(degree-i,T-j):sign*v for (i,j),v in A.items()}
        if transformed != A:
            raise AssertionError(("Reciprocity",k))
        reciprocity_checks += 1
        records.append({
            "k":k,"degree_x":degree,"reciprocity_t_exponent":T,
            "denominator_terms":[list(v) for v in terms],
            "numerator_terms":[[i,j,v] for (i,j),v in sorted(A.items())],
        })
    out = Path(__file__).resolve().parents[1]/"data"
    out.mkdir(exist_ok=True)
    (out/"numerators.json").write_text(json.dumps({
        "convention":"Each term [i,j,c] represents c*x**i*t**j",
        "polynomials":records},indent=2)+"\n",encoding="utf-8")
    with (out/"rho_coefficients.csv").open("w",newline="",encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["k","n","power_of_t","coefficient"])
        for k in range(1,13):
            for n in range(1,21):
                for j,c in enumerate(rho_coefficients(k,n)):
                    writer.writerow([k,n,j,c])
    report = {
        "status":"PASS", "sympy_version":sp.__version__,
        "bivariate_symbolic_determinants":determinant_checks,
        "symbolic_gf_tail_coefficients":gf_tail_checks,
        "symbolic_reciprocity_polynomials":reciprocity_checks,
        "numerator_polynomials_exported":len(records),
        "ranges":{
            "determinants":"1<=k<=6, 1<=n<=4, symbolic u,t",
            "generating_functions":"1<=k<=10, symbolic t; through x^(deg(Q)+8)",
            "rho_data":"1<=k<=12, 1<=n<=20"
        },
        "elapsed_seconds":round(time.perf_counter()-started,3)
    }
    (out/"symbolic_verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
