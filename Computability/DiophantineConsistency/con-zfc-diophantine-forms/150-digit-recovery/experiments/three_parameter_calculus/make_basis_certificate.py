#!/usr/bin/env python3
"""Construct a literal K/S/Peirce proof of the old four-parameter axiom.

The constructor is deliberately separate from verify_research.py, which
accepts only axiom instances and exact modus-ponens references.
"""
from pathlib import Path
import json

def imp(p,q):return (p,q)
def K(p,q):return imp(p,imp(q,p))
def S(p,q,r):return imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))
def P(p,q):return imp(imp(imp(p,q),p),p)

class Proof:
    def __init__(self,formula,rule,left=None,right=None):
        self.formula,self.rule,self.left,self.right=formula,rule,left,right
def ax(f,rule):return Proof(f,rule)
def ass(f):return Proof(f,'assumption')
def mp(minor,major):
    if not isinstance(major.formula,tuple) or major.formula[0]!=minor.formula:
        raise ValueError('ill-typed modus ponens')
    return Proof(major.formula[1],'mp',minor,major)
def identity(a):
    return mp(ax(K(a,a),'K'),mp(ax(K(a,imp(a,a)),'K'),ax(S(a,imp(a,a),a),'S')))
def discharge(a,proof):
    cache={}
    def walk(p):
        if id(p) in cache:return cache[id(p)]
        if p.rule=='assumption' and p.formula==a:r=identity(a)
        elif p.rule=='mp':
            x=p.left.formula;y=p.formula
            r=mp(walk(p.left),mp(walk(p.right),ax(S(a,x,y),'S')))
        else:r=mp(p,ax(K(p.formula,a),'K'))
        cache[id(p)]=r
        return r
    return walk(proof)
def dump(proof):
    steps=[];seen={}
    def walk(p):
        if id(p) in seen:return seen[id(p)]
        refs=[] if p.rule!='mp' else [walk(p.left),walk(p.right)]
        j=len(steps);seen[id(p)]=j
        steps.append({'formula':p.formula,'rule':p.rule,'premises':refs})
        return j
    root=walk(proof)
    return {'schema':'implicational_hilbert_proof_v1','variables':['a','b','c','d'],
            'axioms':['K','S','Peirce'],'steps':steps,'conclusion':root}
def main():
    a,b,c,d='a','b','c','d'
    f=imp(imp(c,d),a);g=imp(a,c);h=b;k=imp(c,d)
    c_from_k=mp(mp(ass(k),ass(f)),ass(g))
    c_closed_k=mp(discharge(k,c_from_k),ax(P(c,d),'P'))
    result=discharge(f,discharge(g,discharge(h,c_closed_k)))
    expected=imp(f,imp(g,imp(b,c)))
    if result.formula!=expected:raise ValueError('wrong final theorem')
    out=dump(result)
    (Path(__file__).resolve().parent/'basis_certificate.json').write_text(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps({'steps':len(out['steps']),'conclusion':out['conclusion']}))
if __name__=='__main__':main()
