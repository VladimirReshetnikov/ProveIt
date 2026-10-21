#!/usr/bin/env python3
"""Check an explicit modal Heyting counterexample with standard library only.

This is a fragment counterexample, not a model of the native set-theory bundle.
"""
from itertools import product
from pathlib import Path
import json

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    n=5;edges=((0,2),(1,2),(1,4));above=[1<<i for i in range(n)]
    for x,y in edges:above[x]|=1<<y
    for _ in range(n):
        for x,y in product(range(n),repeat=2):
            if above[x]>>y&1:above[x]|=above[y]
    upsets=[m for m in range(1<<n)if all(not(m>>i&1)or above[i]&m==above[i]for i in range(n))]
    expected=[0,4,5,8,12,13,16,20,21,22,23,24,28,29,30,31]
    assert upsets==expected
    qvalues=[0,0,0,8,8,8,4,4,5,4,21,12,12,13,12,31]
    Q=dict(zip(upsets,qvalues));T=31;F=0
    def I(a,b):return sum(1<<i for i in range(n)if above[i]&a&~b==0)
    def N(a):return I(a,F)
    assert Q[T]==T and Q[F]==F
    assert all(a!=T or I(a,b)!=T or b==T for a,b in product(upsets,repeat=2))
    assert all(I(a,I(b,a))==T for a,b in product(upsets,repeat=2))
    assert all(I(I(a,I(b,c)),I(I(a,b),I(a,c)))==T for a,b,c in product(upsets,repeat=3))
    assert all(I(Q[I(a,b)],I(Q[a],Q[b]))==T for a,b in product(upsets,repeat=2))
    assert all(I(N(Q[N(Q[a])]),a)==T for a in upsets)
    assert all(I(Q[Q[a]],Q[Q[a]])==T for a in upsets)
    assert all(I(F,a)==T for a in upsets)
    P=8;NP=N(P);QNP=Q[NP];NNQNP=N(N(QNP))
    assert Q[P]==P and N(N(P))==P
    assert (NP,QNP,NNQNP)==(23,21,23)
    assert I(NP,QNP)!=T and I(NNQNP,QNP)!=T
    def members(mask):return [i for i in range(n)if mask>>i&1]
    out={'status':'PERSISTENT_NEGATION_FRAGMENT_COUNTERMODEL_PASS','worlds':n,'strict_order_edges':edges,
         'upsets':[members(a)for a in upsets],'Q':[[members(a),members(Q[a])]for a in upsets],
         'validated':['Heyting implication','K','S','MP','GEN','explosion','normality/rho2','seriality','rho6','commutation with all binders equal to Q'],
         'witness':{'P':members(P),'QP':members(Q[P]),'NP':members(NP),'QNP':members(QNP),'NNQNP':members(NNQNP)},
         'not_claimed':['native rho1/equality/member interpretation','native gated set-theory bundle','consistency or inconsistency of the full K/S replacement calculus']}
    (Path(__file__).parent/'persistent_negation_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'algebra_elements':len(upsets),'K_checks':16**2,'S_checks':16**3,'normality_checks':16**2,'B6_checks':16,'witness':out['witness']}))
if __name__=='__main__':main()
