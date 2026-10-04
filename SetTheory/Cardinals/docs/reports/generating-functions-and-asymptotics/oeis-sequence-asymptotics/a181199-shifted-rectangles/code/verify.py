#!/usr/bin/env python3
"""Run exact finite checks; no conjectured OEIS recurrence is used."""
from __future__ import annotations
import json
import time
from fractions import Fraction as F
from math import comb, factorial, prod
from pathlib import Path
from tableaux import (count, all_prefixes, shifted_hook, brute_poset,
                      interior_probability, unrestricted_word_count)
from coefficients import coefficients, moment
ROOT=Path(__file__).resolve().parents[1]

def main():
    start=time.time(); checks=[]
    def add(name,num):
        print(f'PASS: {name}: {num} checks',flush=True)
        checks.append({'suite':name,'checks':num,'status':'PASS'})
    num=0
    for m in range(1,6):
        for n in range(1,7):
            if m*n<=22:
                assert count(m,n)==brute_poset(m,n),(m,n)
                num+=1
    add('independent bitmask-poset and row-count enumeration',num)
    num=0
    for m in range(1,6):
        for n in range(1,9):
            pref=all_prefixes(m,n); T=pref[(n,)*m]
            split=0; interior_split=0
            for shape,g in pref.items():
                comp=tuple(n-x for x in reversed(shape))
                term=comb(m*n,sum(shape))*g*pref[comp]
                split+=term
                if shape[0]<n and shape[-1]>0:
                    assert shifted_hook(shape)==g,(shape,g)
                    num+=1
                    interior_split+=term
            assert split==T*2**(m*n)
            I=interior_probability(m,n)
            M=unrestricted_word_count(m,n)
            assert I==F(interior_split,2**(m*n)*M)
            assert F(0)<=F(T,M)-I<=F(2*m,2**n)
    add('interior shifted-hook prefix counts',num)
    add('exact random-threshold split, rational interior sum and boundary bounds',40*3)
    num=0
    for n in range(1,31):
        assert count(2,n)==comb(2*n-2,n-1)//n
        num+=1
    add('Catalan control T_2(n)=C_(n-1)',num)
    refs=json.loads((ROOT/'data/oeis_selected.json').read_text())
    generated={}
    for name,entry in refs.items():
        if not name.startswith("A"):continue
        values={}
        for n,a in entry['terms'].items():
            if int(n)<=40:
                got=count(entry['height'],int(n));assert got==int(a),(name,n)
                values[n]=str(got)
        generated[name]=values
        add(name+' reference values regenerated independently',len(values))
    (ROOT/'data/exact_regenerated.json').write_text(json.dumps(generated,indent=2)+'\n')
    data={}
    for m in range(1,7):
        c,b=coefficients(m,5)
        assert c[0]==1
        assert c[1]==F(m*(m*m-1),12)
        assert c[2]==F(m*m*(m*m-1)*(m*m+2),288)
        assert b[1]==F((m*m-1)**2,12*m)
        assert b[2]==F((m*m-1)*(m**6+3*m*m-1),288*m*m)
        if m==2:assert c==[F(1,2**j) for j in range(6)]
        data[str(m)]={'c':[str(v) for v in c],'b':[str(v) for v in b]}
    add('all-order engine against universal first/second corrections (m=1..6)',30)
    assert moment(4,2)==(F(3),F(-2),F(0))
    assert moment(6,2)==(F(15),F(-30),F(16))
    add('standardized binomial moment controls',2)
    (ROOT/'data/coefficients_m1_to_m6.json').write_text(json.dumps(data,indent=2)+'\n')
    result={'status':'PASS','suites':checks,'total_checks':sum(x['checks'] for x in checks),
            'seconds':round(time.time()-start,3),
            'scope':'Finite exact tests corroborate but do not replace the proofs. Values at n=80 are reference data, not regenerated.'}
    (ROOT/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
