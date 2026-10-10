"""Reproduce exact and independent numerical mixed-point checks.

Usage from the package root:
    python code/verify_mixed.py --dps 80

The default run verifies 16 exact partial-fraction decompositions, 10
explicit symbolic specializations, 12 general-index quadratures, and the
18 relevant projections in the archived 90-digit height-one quadratures.
Use --rerun-height-one to recompute all 27 archived height-one integrals.
Numerical residuals are diagnostic and are not certified error bounds.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import mpmath as mp
import sympy as sp

from mixed_parity import (
    height_one_exact, height_one_numeric, mixed_integral,
    parity_coefficients, parity_numeric, partial_fraction_symbolic,
)


def explicit_identities():
    """Separately transcribed displayed formulas; exact comparison catches typos."""
    p, z, l, q = sp.pi, sp.zeta, sp.log, sp.Rational
    B = lambda s: sp.Symbol(f"beta_{s}")
    C = lambda s: sp.Symbol(f"C_{s}")
    return {
        (4, 4): -q(587, 1024)*z(5)+p**2*z(3)/64+3*p**4*l(2)/512,
        (5, 4): 3*B(6)-z(2)*B(4)-z(4)*B(2)-5*p**5*l(2)/3072,
        (4, 3): -q(281, 162)*z(5)+2*p**2*z(3)/27+2*p**4*l(3)/243,
        (5, 3): -3*C(6)+z(2)*C(4)+z(4)*C(2)+p**5*l(3)/729,
        (6, 4): -q(8633, 16384)*z(7)+5*p**2*z(5)/1024
                +p**4*z(3)/960+11*p**6*l(2)/20480,
        (7, 4): 4*B(8)-z(2)*B(6)-z(4)*B(4)-z(6)*B(2)
                -61*p**7*l(2)/368640,
        (6, 3): -q(3277, 1458)*z(7)+20*p**2*z(5)/243
                +2*p**4*z(3)/405+26*p**6*l(3)/32805,
        (7, 3): -4*C(8)+z(2)*C(6)+z(4)*C(4)+z(6)*C(2)
                +14*p**7*l(3)/98415,
        (8, 4): -q(133367, 262144)*z(9)+21*p**2*z(7)/16384
                +p**4*z(5)/3072+p**6*z(3)/10080+731*p**8*l(2)/13762560,
        (8, 3): -q(4009, 1458)*z(9)+182*p**2*z(7)/2187
                +4*p**4*z(5)/729+4*p**6*z(3)/8505+164*p**8*l(3)/2066715,
    }


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--output", type=Path, default=root/"results"/"mixed_verification.json")
    parser.add_argument("--rerun-height-one", action="store_true")
    args = parser.parse_args()
    if args.dps < 40:
        raise ValueError("Use at least 40 decimal digits for these checks")
    mp.mp.dps = args.dps
    threshold = mp.mpf(10) ** (-(args.dps-15))

    n, h = sp.symbols("n h", nonzero=True)
    exact_pf = []
    for a in range(2, 6):
        for b in range(1, 5):
            difference = sp.cancel(1/(n**b*(n-h)**a)-partial_fraction_symbolic(a,b,n,h))
            assert difference == 0, (a,b,difference)
            exact_pf.append({"a": a, "b": b, "exact_difference": "0"})

    exact_display = []
    for (a, level), rhs in explicit_identities().items():
        difference = sp.simplify(height_one_exact(a,level)-rhs)
        assert difference == 0, (a,level,difference)
        exact_display.append({"a": a, "level": level, "exact_difference": "0"})

    points = {
        "gaussian": mp.j,
        "eisenstein": mp.exp(4*mp.pi*mp.j/3),
        "theta_0.731": mp.exp(mp.mpf("0.731")*mp.j),
        "theta_1.2": mp.exp(mp.mpf("1.2")*mp.j),
        "theta_2.4": mp.exp(mp.mpf("2.4")*mp.j),
    }
    cases = [(2,2,"gaussian"), (2,3,"eisenstein"), (2,4,"theta_0.731"),
             (3,2,"eisenstein"), (3,3,"gaussian"), (3,4,"theta_1.2"),
             (4,2,"theta_2.4"), (4,3,"gaussian"), (4,4,"eisenstein"),
             (5,2,"gaussian"), (5,3,"eisenstein"), (5,4,"theta_0.731")]
    general = []
    for a,b,label in cases:
        value = mixed_integral(a,b,points[label])
        lhs = value-(-1)**(a+b)*mp.conj(value)
        rhs = parity_numeric(a,b,points[label])
        error = abs(lhs-rhs)
        assert error < threshold, (a,b,label,mp.nstr(error))
        general.append({"a": a, "b": b, "point": label,
                        "real": mp.nstr(mp.re(value),args.dps-5),
                        "imag": mp.nstr(mp.im(value),args.dps-5),
                        "absolute_error": mp.nstr(error,10)})

    archived_path = root/"results"/"height_one_quadrature.json"
    archived_checks = []
    if archived_path.exists():
        data = json.loads(archived_path.read_text())
        for row in data["checks"]:
            if row["point"] not in ("gaussian","eisenstein"):
                continue
            a = row["a"]
            level = 4 if row["point"] == "gaussian" else 3
            key = "value_real" if a%2 == 0 else "value_imag"
            error = abs(mp.mpf(row[key])-height_one_numeric(a,level))
            # Archived numbers contain 80 significant digits from 90-digit runs.
            assert error < max(threshold,mp.mpf("1e-75")), (a,level,error)
            archived_checks.append({"a": a, "level": level,
                                    "absolute_error": mp.nstr(error,10)})

    rerun = []
    if args.rerun_height_one:
        for label in ("gaussian","eisenstein","theta_0.731"):
            for a in range(2,11):
                value = mixed_integral(a,1,points[label])
                lhs = value-(-1)**(a+1)*mp.conj(value)
                error = abs(lhs-parity_numeric(a,1,points[label]))
                assert error < threshold, (a,label,error)
                rerun.append({"a": a, "point": label,
                              "absolute_error": mp.nstr(error,10)})

    all_formulas = [
        {"a": a, "level": level,
         "projection": "real" if a%2 == 0 else "imaginary",
         "formula": str(height_one_exact(a,level)),
         "latex": sp.latex(height_one_exact(a,level))}
        for level in (3,4) for a in range(2,11)
    ]
    result = {
        "status": "all checks passed",
        "precision_decimal_digits": args.dps,
        "numerical_assertion_threshold": mp.nstr(threshold),
        "numerical_status": "Diagnostic high-precision checks, not interval-certified error bounds",
        "exact_partial_fraction_checks": exact_pf,
        "exact_displayed_identity_checks": exact_display,
        "general_index_quadrature_checks": general,
        "archived_height_one_projection_checks": archived_checks,
        "optional_height_one_rerun": rerun,
        "height_one_formulas": all_formulas,
        "sample_exact_coefficient_data": [parity_coefficients(a,b) for a,b,_ in cases],
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    table = args.output.with_suffix(".csv")
    with table.open("w",newline="") as f:
        writer = csv.DictWriter(f,fieldnames=["a","b","point","real","imag","absolute_error"])
        writer.writeheader()
        writer.writerows(general)
    print(json.dumps({"status": result["status"],
                      "exact_partial_fraction_checks": len(exact_pf),
                      "exact_displayed_identity_checks": len(exact_display),
                      "general_index_quadrature_checks": len(general),
                      "archived_height_one_projection_checks": len(archived_checks),
                      "maximum_general_index_error": max(float(r["absolute_error"]) for r in general),
                      "json": str(args.output),"csv": str(table)},indent=2))


if __name__ == "__main__":
    main()
