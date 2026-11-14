#!/usr/bin/env python3
"""Exact numeric contradiction certificate for the unchanged coefficient-three calculus.

K and S are explicitly derived-rule dependencies, justified by the supplied
parameter-generic RestrictedImplication.lean (copied under reference/).
This checks a complete fourteen-line certificate in that conservative derived
rule extension; it is not an independent compilation of the generic Lean proof.
"""
import hashlib,json
from pathlib import Path
if not __debug__:
    raise RuntimeError('Run with assertions enabled; do not use Python -O.')
HERE=Path(__file__).resolve().parent

def pair(a,b):return (a+b)*(a+b+1)//2+b
def I(a,b):return 3*pair(a,b)
def E(a,b):return 3*pair(a,b)+3
def U(a,b):return 3*pair(b,a)+2
def N(a):return I(a,1)
def K(a,b):return I(a,I(b,a))
def S(a,b,c):return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def H5(d,h):return N(U(d,N(E(h,d))))

def build():
    proof=[]
    def add(rule,args,conclusion):
        proof.append(dict(line=len(proof)+1,rule=rule,args=list(args),conclusion=conclusion))
        return len(proof)
    def mp(major,minor,conclusion):return add('mp',(major,minor),conclusion)
    truth=add('rho8',(0,0,0,0),R(0,0,0,0))
    a=I(0,1);aa=I(a,a)
    p=add('K',(a,aa),K(a,aa))
    q=add('K',(a,a),K(a,a))
    r=add('S',(a,I(a,a),a),S(a,I(a,a),a))
    r=mp(r,p,I(K(a,a),I(a,a)))
    identity=mp(r,q,I(a,a))
    r=add('K',(0,a),K(0,a))
    a_truth=mp(r,truth,I(a,0))
    r=add('S',(a,0,1),S(a,0,1))
    r=mp(r,identity,I(I(a,0),I(a,1)))
    neg_a=mp(r,a_truth,N(a))
    universal=add('gen',(0,neg_a),U(0,N(a)))
    axiom=add('head5',(0,1),H5(0,1))
    mp(axiom,universal,1)
    return proof

def check(proof):
    values=[]
    for index,row in enumerate(proof,1):
        assert row['line']==index
        rule,args,conclusion=row['rule'],row['args'],row['conclusion']
        assert isinstance(conclusion,int)and conclusion>=0
        def previous(i):
            assert isinstance(i,int)and 1<=i<index
            return values[i-1]
        if rule=='rho8':
            a,b,c,u=args
            assert u<=a and conclusion==R(a,b,c,u)
        elif rule=='K':assert conclusion==K(*args)
        elif rule=='S':assert conclusion==S(*args)
        elif rule=='head5':assert conclusion==H5(*args)
        elif rule=='gen':
            binder,source=args
            assert conclusion==U(binder,previous(source))
        elif rule=='mp':
            major,minor=args
            assert previous(major)==I(previous(minor),conclusion)
        else:raise AssertionError('unknown rule')
        values.append(conclusion)
    assert values[-1]==1
    assert R(0,0,0,0)==0
    assert E(1,0)==I(0,1)==6
    assert N(6)==87 and U(0,N(6))==11486
    assert H5(0,1)==I(11486,1)
    return dict(status='PASS',proof_lines=len(proof),conclusion=values[-1],
        exact_values={'truth':0,'E3(1,0)':E(1,0),'I3(0,1)':I(0,1),
                      'N3(6)':N(6),'U3(0,N3(6))':U(0,N(6)),
                      'head5(0,1)':H5(0,1)},
        derived_rule_dependencies=['M6.Logic.RestrictedImplication.k',
                                   'M6.Logic.RestrictedImplication.s'],
        generic_source_sha256=hashlib.sha256((HERE/'reference/RestrictedImplication.lean').read_bytes()).hexdigest(),
        scope='Exact fourteen-line arithmetic certificate using explicitly retained derived K/S rules; no Lean compilation claimed')

if __name__=='__main__':
    proof=build()
    result=check(proof)
    (HERE/'proof.json').write_text(json.dumps(proof,indent=2)+'\n')
    (HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
