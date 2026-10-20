#!/usr/bin/env python3
"""Independent finite verification for the strengthened HC countermodel.

This matrix validates all five simple restrictions simultaneously, even
with identity, ex-falso, and K.  The infinite HC model is a separate ordinary
mathematical proof in restricted_rho8_strong_countermodel.md.
"""
import itertools,json
from pathlib import Path

TABLE=((3,3,3,3),(3,3,1,3),(3,3,3,3),(0,0,0,3))
VALUES=range(4)
I=lambda a,b:TABLE[a][b]
N=lambda a:I(a,0)
And=lambda a,b:N(I(a,N(b)))
All=lambda xs:3 if all(x==3 for x in xs)else 0
Ex=lambda xs:N(All([N(x)for x in xs]))
L=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))

def main():
    pairs=list(itertools.product(VALUES,repeat=2))
    triples=list(itertools.product(VALUES,repeat=3))
    restrictions={'F':lambda a,b,c:0,'truth':lambda a,b,c:3,
                  'a':lambda a,b,c:a,'b':lambda a,b,c:b,'c':lambda a,b,c:c}
    assert all(L(a,b,c,f(a,b,c))==3 for f in restrictions.values()for a,b,c in triples)
    assert all(I(a,a)==I(0,a)==3 for a in VALUES)
    assert all(I(a,I(b,a))==3 for a,b in pairs)
    assert all(not(a==3 and I(a,b)==3)or b==3 for a,b in pairs)
    assert all((And(a,b)==3)==(a==3 and b==3)for a,b in pairs)
    assert all(And(a,b)in(0,3)for a,b in pairs)
    assert all((I(a,b)==3)==(a!=3 or b==3)for a in VALUES for b in(0,3))
    normality_cases=0
    for length in(1,2,3):
        vectors=list(itertools.product(VALUES,repeat=length))
        for aa in vectors:
            assert (Ex(aa)==3)==any(a==3 for a in aa)
            assert all(I(All(aa),a)==3 for a in aa)
            for bb in vectors:
                assert I(All([I(a,b)for a,b in zip(aa,bb)]),I(All(aa),All(bb)))==3
                normality_cases+=1
    assert I(1,2)==1!=3
    antichain=[tuple(x for bit in w for x in(bit,1-bit))for w in itertools.product((0,1),repeat=4)]
    assert all(any(x==0 and y==1 for x,y in zip(p,u))for p in antichain for u in antichain if p!=u)
    assert L(0,3,1,2)==0
    assert I(I(1,I(0,2)),I(I(1,0),I(1,2)))==0
    result=dict(status='FINITE_ALGEBRA_CLAIMS_PASS',matrix=TABLE,designated=3,falsum=0,
                restricted_schemes=list(restrictions),restricted_instances=5*len(triples),
                identity=True,ex_falso=True,K=True,modus_ponens=True,
                Boolean_consequent_implication=True,Boolean_conjunction=True,
                normality_vector_cases=normality_cases,
                unrestricted_L_counterexample=[0,3,1,2],S_counterexample=[1,0,2],
                scope='Finite algebra only; the HC domain and native seed-K soundness are proved separately.')
    path=Path(__file__).resolve().parent/'generated/restricted_rho8_strong_countermodel.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
