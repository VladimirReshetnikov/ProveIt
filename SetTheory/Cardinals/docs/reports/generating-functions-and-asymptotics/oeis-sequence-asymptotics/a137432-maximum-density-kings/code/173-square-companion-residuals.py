"""Optional high-precision residual diagnostics, using only decimal.

These evaluate published fixture terms, not freshly computed n=100..800 counts.
No finite residual table establishes an asymptotic error bound or coefficient.
"""
import argparse
import json
from decimal import Decimal, localcontext
from pathlib import Path

from coefficient_certificates import CLAIMED


def compute(precision=80):
    if precision < 40:
        raise ValueError("Use at least 40 decimal digits")
    fixture = json.loads((Path(__file__).parent / "fixtures/a137432_selected.json").read_text())
    with localcontext() as ctx:
        ctx.prec = precision
        e = Decimal(1).exp()
        q = 1/e
        constant = 2*e*(e-1)**2/(e-2)**2
        coefficients = []
        for rational in CLAIMED:
            numerator = sum((Decimal(c.numerator)/Decimal(c.denominator))*q**i
                            for i,c in enumerate(rational.p))
            coefficients.append(numerator / ((1-q)**rational.a*(1-2*q)**rational.b))
        rows = []
        for n in (100, 200, 400, 800):
            dn = Decimal(n)
            normalized = Decimal(fixture["terms"][str(n)]) / (constant*dn**n)
            r1 = normalized - 1 - coefficients[1]/dn
            r2 = r1 - coefficients[2]/dn**2
            r3 = r2 - coefficients[3]/dn**3
            rows.append({"n":n, "normalized":str(normalized),
                         "n2_after_c1":str(dn**2*r1), "n3_after_c2":str(dn**3*r2),
                         "after_c3":str(r3)})
        return {"precision":precision,"C":str(constant),
                "coefficients":[str(c) for c in coefficients],"residuals":rows,
                "interpretation":"Diagnostic evaluation of selected published terms; not an asymptotic proof."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=80)
    args = parser.parse_args()
    print(json.dumps(compute(args.precision), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
