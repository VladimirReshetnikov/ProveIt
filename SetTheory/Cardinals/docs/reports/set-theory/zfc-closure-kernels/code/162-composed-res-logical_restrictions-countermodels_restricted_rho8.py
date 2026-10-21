#!/usr/bin/env python3
"""Exact finite-matrix obstructions to naive restricted implicational bases.

The result concerns only truth, MP, and the displayed restricted rho8 schema.
It is not a countermodel to the full numerical set-theoretic calculus.
"""
from itertools import product
import json
from pathlib import Path

def countermodel(label,n):
    universe=range(n)
    # T=0 is the sole designated value. MP requires row 0 to be nonzero
    # at each nonzero column; I(T,T)=T is preserved exactly.
    for rest0 in product(range(1,n),repeat=n-1):
        for rest in product(universe,repeat=n*(n-1)):
            table=(0,)+rest0+rest
            I=lambda x,y:table[n*x+y]
            ok=True
            for a,b,c in product(universe,repeat=3):
                u={'U=A':a,'U=B':b,'U=C':c,'U=0':0}[label]
                if I(I(I(c,u),a),I(I(a,c),I(b,c)))!=0:
                    ok=False;break
            if not ok:continue
            bad=[]
            for p,q in product(universe,repeat=2):
                if I(p,I(q,p))!=0:bad.append({'theorem':'K','p':p,'q':q,'value':I(p,I(q,p))})
                if I(I(I(p,q),p),p)!=0:bad.append({'theorem':'Peirce','p':p,'q':q,'value':I(I(I(p,q),p),p)})
            if bad:
                return {'restriction':label,'size':n,'truth':0,'designated':[0],
                        'implication_table':[list(table[k*n:(k+1)*n]) for k in universe],
                        'counterexamples':bad,
                        'scope':'Only the implicational fragment {truth, MP, restricted rho8}; full native rows and bundle are not modeled.'}
    return None

def independently_check(m):
    n=m['size'];t=m['implication_table'];I=lambda a,b:t[a][b]
    assert I(0,0)==0
    assert all(a!=0 or I(a,b)!=0 or b==0 for a,b in product(range(n),repeat=2))
    for a,b,c in product(range(n),repeat=3):
        u={'U=A':a,'U=B':b,'U=C':c,'U=0':0}[m['restriction']]
        assert I(I(I(c,u),a),I(I(a,c),I(b,c)))==0
    for b in m['counterexamples']:
        p,q=b['p'],b['q']
        v=I(p,I(q,p)) if b['theorem']=='K' else I(I(I(p,q),p),p)
        assert v==b['value']!=0

if __name__=='__main__':
    out=[]
    for label in ('U=A','U=B','U=C','U=0'):
        result=None
        for n in (2,3):
            result=countermodel(label,n)
            if result:break
        if result:independently_check(result)
        out.append(result or {'restriction':label,'status':'No countermodel found in the searched family'})
    Path(__file__).with_name('restricted_rho8_countermodels.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
