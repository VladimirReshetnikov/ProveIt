#!/usr/bin/env python3
"""Produce exact sequence data and high-precision coefficient asymptotics.
Standard library only; no Somos recurrence is used to produce sequence data.
"""
from pathlib import Path
from decimal import Decimal, localcontext
import json
from verify_certificates import family, moments, hankels

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT/"data"
DATA.mkdir(exist_ok=True)
for r in (0, 1, 2, 3, 4):
    A, B, D, P = family(12)
    a = moments([p.at(r) for p in A], [p.at(r) for p in B], 64)
    h = hankels(a, 32)
    for name, seq, start in (("moments", a, 0), ("hankels", h, -1)):
        text = f"# Family C12, r={r}; {name}; exact independent determinants\n"
        text += "".join(f"{n} {v}\n" for n, v in enumerate(seq, start))
        (DATA/f"C12_r{r}_{name}.txt").write_text(text)

with localcontext() as ctx:
    ctx.prec = 80
    r = Decimal(2)
    lo, hi = Decimal(0), Decimal(1)/r
    for _ in range(300):
        x = (lo+hi)/2
        if x == lo or x == hi:
            break
        val = x+x*x/(1-r*x)+2*x*x.sqrt()-1
        if val < 0:
            lo = x
        else:
            hi = x
    rho = (lo+hi)/2
    x = rho
    L = x+x*x/(1-r*x)
    L1 = 1+(2*x-r*x*x)/(1-r*x)**2
    L2 = 2/(1-r*x)**3
    delta1 = -2*(1-L)*L1-12*x*x
    delta2 = 2*L1*L1-2*(1-L)*L2-24*x
    lam = (-rho*delta1).sqrt()/(2*rho**3)
    pi = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
    C = lam/(2*pi.sqrt())
    R1 = 3-rho*delta2/(4*delta1)
    correction = Decimal(3)/8-Decimal(3)/2*R1
    A, B, _, _ = family(12)
    a = moments([p.at(2) for p in A], [p.at(2) for p in B], 400)
    rows = []
    for n in (25, 50, 100, 200, 400):
        dn = Decimal(n)
        ratio = Decimal(a[n])*(rho**n)*dn*dn.sqrt()/C
        corrected = ratio/(1+correction/dn)
        rows.append({"n": n, "scaled_ratio_to_leading_term": str(ratio),
                     "ratio_to_first_corrected_term": str(corrected)})
    output = {"family": 12, "r": 2, "rho": str(rho), "growth_constant": str(1/rho),
              "C": str(C), "first_relative_correction": str(correction),
              "precision_decimal_digits": 80, "rows": rows,
              "note": "Asymptotics of moments a_n, NOT of Hankel determinants h_n."}
    (DATA/"asymptotics_C12_r2.json").write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2))
