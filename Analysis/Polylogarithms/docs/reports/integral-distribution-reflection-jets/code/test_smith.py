#!/usr/bin/env python3
"""Optional independent integer Smith-form checks (requires SymPy)."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
from distribution import Distribution, reflected_torsion

ROOT=Path(__file__).resolve().parents[1]
if not __debug__:
    raise RuntimeError('Run without -O: the regression suite uses assertions.')

def main():
    total=0;examples=[]
    levels=(3,4,6,8,9,10,12,15,18,20,24,30,36,45,60)
    for q in levels:
        d=Distribution(q);size=len(d.basis)
        for weights in product((-1,0,1,2),repeat=len(d.primes)):
            c=sp.zeros(size)
            for j,a in enumerate(d.basis):
                for b,v in d.normal_form(-a%q).items():
                    c[d.index[b],j]=v.evaluate(weights)
            assert c*c==sp.eye(size)
            t=reflected_torsion(q,dict(zip(d.primes,weights)))
            target=[1]*(size//2-t)+[2]*t+[0]*(size//2)
            for sign in (1,-1):
                snf=smith_normal_form(c-sign*sp.eye(size),domain=ZZ)
                got=[abs(int(snf[i,i])) for i in range(size)]
                assert got==target,(q,weights,sign,got,target)
                total+=1
                if q in (4,12,15,60) and all(v==1 for v in weights):
                    examples.append({'level':q,'weights':list(weights),'reflection_sign':sign,
                                     'smith_diagonal':got})
    out={'status':'PASS','smith_forms_checked':total,'sympy_version':sp.__version__,
         'levels':list(levels),'weights_per_prime':[-1,0,1,2],'examples':examples}
    (ROOT/'logs/smith_tests.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='examples'},indent=2))

if __name__=='__main__':main()
