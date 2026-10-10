#!/usr/bin/env python3
"""Exact cyclotomic product checks and deliberately corrupted-certificate controls."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sympy as sp
from verify_certificates import verify
ROOT=Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')


def main():
    X=sp.Symbol('X');products=[]
    for q,exponents,value in [(12,{1:1,5:1,9:2},2),
                              (30,{1:1,8:1,12:1,14:1,18:2,20:2,24:1},15)]:
        P=sp.Poly(sp.prod((1-X**a)**m for a,m in exponents.items())-value,X,domain=sp.ZZ)
        Phi=sp.Poly(sp.cyclotomic_poly(q,X),X,domain=sp.ZZ)
        Q,R=sp.div(P,Phi)
        assert R.is_zero and P==Q*Phi
        products.append(dict(q=q,exponents=exponents,value=value,
             cyclotomic_coefficients_ascending=list(reversed([int(c) for c in Phi.all_coeffs()])),
             quotient_coefficients_ascending=list(reversed([int(c) for c in Q.all_coeffs()])),
             remainder_zero=True))
    controls=[]
    original=json.loads((ROOT/'data'/'normal_forms_q12.json').read_text())
    with TemporaryDirectory() as tmp:
        for mode in ['coefficient','basis','parent']:
            d=json.loads(json.dumps(original))
            if mode=='coefficient':d['normal_forms']['1'][0][2]+=2
            if mode=='basis':d['basis'][1]=6
            if mode=='parent':d['selected_rows'][0]['parent']=(d['selected_rows'][0]['parent']+1)%12
            p=Path(tmp)/f'{mode}.json';p.write_text(json.dumps(d))
            try:verify(p)
            except (AssertionError,ValueError,KeyError) as exc:
                controls.append(dict(corruption=mode,rejected=True,diagnostic=str(exc)[:180]))
            else:raise ArithmeticError(f'corruption control was accepted: {mode}')
    (ROOT/'data'/'products_and_controls.json').write_text(json.dumps(
        dict(products=products,corruption_controls=controls),indent=2)+'\n')
    print(json.dumps(dict(exact_products=len(products),rejected_corruptions=len(controls)),indent=2))
if __name__=='__main__':main()
