#!/usr/bin/env python3
"""Exact finite row-certificate replay and independent integral diagnostics."""
from pathlib import Path
import json
import mpmath as mp
import sympy as sp
from verify_rank import product_matrix

records = []
for w in range(4, 21, 2):
    A, coords, tags = product_matrix(w)
    by_tag = {tuple(tag):j for j,tag in enumerate(tags)}
    coefficients = {}

    def add(p,q,r,s,kind,c):
        j=by_tag[(p,q,r,s,kind)]
        coefficients[j]=coefficients.get(j,0)+c

    for p in range(1,w):
        q=w-p
        add(p,q,2,1,"stuffle",1)
        add(p,q,2,1,"shuffle",(-1)**(q-1))
    add(1,w-1,2,1,"shuffle",1)
    add(1,w-1,2,1,"stuffle",1)
    add(w-1,1,1,1,"stuffle",-1)
    add(1,w-1,1,3,"shuffle",-1)
    actual=sp.zeros(1,A.cols)
    for j,c in coefficients.items():
        actual += c*A.row(j)
    target=sp.zeros(1,A.cols)
    target[coords.index((w-1,1,1,2))]=2
    assert actual == target
    records.append({"weight":w,"coefficient_residual_exactly_zero":True,
                    "nonzero_row_coefficients":[{"row_tag":list(tags[j]),
                                                 "coefficient":c}
                                                for j,c in coefficients.items() if c]})

mp.mp.dps=70
beta=lambda s: mp.im(mp.polylog(s,1j))
eta=lambda s: mp.log(2) if s==1 else (1-mp.power(2,1-s))*mp.zeta(s)
diagnostics=[]
for w in (2,4,6,8,10):
    value=mp.im(mp.quad(
        lambda t:(-mp.log(t))**(w-2)/mp.factorial(w-2)
                 *(-1j)*mp.log(1+1j*t)/(1-1j*t),
        [0,mp.mpf("0.1"),mp.mpf("0.5"),1]))
    rhs=(mp.mpf(w)/2)*beta(w)-mp.log(2)*beta(w-1) \
        -sum(eta(a)*beta(w-a) for a in range(1,w,2)) \
        +mp.power(2,1-w)*beta(1)*eta(w-1)
    assert abs(value-rhs) < mp.mpf("1e-65")
    diagnostics.append({"weight":w,"integral_value":mp.nstr(value,65),
                        "identity_value":mp.nstr(rhs,65),
                        "numerical_difference":mp.nstr(value-rhs,8),
                        "certified_interval":False})

receipt={"exact_row_certificates":records,
         "independent_integral_diagnostics":diagnostics,
         "precision_digits":mp.mp.dps,
         "scope":"Exact identities follow from the row certificates and proof; floating-point quadrature is only a diagnostic."}
output=Path(__file__).with_name("mixed_family_receipt.json")
output.write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({"exact_certificates":len(records),"weights":[r["weight"] for r in records],
                  "integral_diagnostics":len(diagnostics),"output":str(output)}))
