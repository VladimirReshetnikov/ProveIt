#!/usr/bin/env python3
"""Numerical diagnostics; these are not interval certificates of global optimality."""
from __future__ import annotations
import csv
import json
from pathlib import Path
import mpmath as mp
from endpoint import solve_endpoint, rational_parameter, block_matrix, expansion

ROOT = Path(__file__).resolve().parents[1]

def weighted_cut(block, q, p):
    weights = [q, 1-q]
    vals = []
    for a in range(4):
        for b in range(4):
            vals.append(abs(sum(weights[i]*weights[j]*(block[i][j]-p)
                for i in range(2) for j in range(2) if (a>>i)&1 and (b>>j)&1)))
    return max(vals)

def main():
    mp.mp.dps = 80
    rows=[]; tests=0; max_error=mp.mpf(0)
    for ts in ('0.2','0.1','0.05','0.02','0.01','0.005'):
        for sign in (-1,1):
            e=solve_endpoint(ts, sign, 80)
            r=mp.sqrt(e.q/(1-e.q))
            other=rational_parameter(r, sign, 80)
            err=max(abs(e.t-other.t),abs(e.u-other.u),abs(e.v-other.v),abs(e.value-other.value))
            assert err < mp.mpf('1e-60')
            max_error=max(max_error,err)
            B=block_matrix(e,p='0.5')
            assert all(0 < v < 1 for row in B for v in row)
            delta=weighted_cut(B,e.q,mp.mpf('.5'))
            assert abs(delta-e.value/2)<mp.mpf('1e-60')
            row=e.as_dict(55)
            row['correction_over_t3']=mp.nstr((e.value-e.t/4)/e.t**3,55)
            row['parametrization_error']=mp.nstr(err,8)
            rows.append(row);tests+=1
            if sign==-1:
                for n in (6,10,20,50,100,1000):
                    qn=mp.nint(n*e.q)/n
                    Bn=block_matrix(e,p='0.5',q=qn)
                    value=weighted_cut(Bn,qn,mp.mpf('.5'))
                    loss=e.value/2-value
                    assert loss>=-mp.mpf('1e-60')
                    assert loss<=3*(e.t/2)/(4*n*n)+mp.mpf('1e-60')
                    tests+=1
    out=ROOT/'results'
    out.mkdir(exist_ok=True)
    (out/'numeric_diagnostics.json').write_text(json.dumps({
        'status':'PASS','arithmetic':'mpmath, 80 decimal digits',
        'checks':tests,'maximum_independent_parametrization_error':mp.nstr(max_error,12),
        'warning':'Numerical diagnostics only; no certified positive theorem radius is inferred.',
        'rows':rows},indent=2)+'\n')
    with (out/'endpoint_values.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    print('PASS:',tests,'diagnostic groups; independent parameter error',mp.nstr(max_error,8))
    for row in rows:
        if row['sign']==-1:
            print('t=',row['t'],'value=',row['value'][:22],
                  'correction/t^3=',row['correction_over_t3'][:14],
                  'remainder/t^6=',row['normalized_remainder_after_t5'][:14])

if __name__=='__main__':main()
