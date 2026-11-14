#!/usr/bin/env python3
"""Partial syntactic PA-provability certificates for startup proof stores.

This is not an arithmetic truth predicate or a complete PA proof checker.
Each accepted true/false label has one of the explicit proof templates in
startup_seed_lemma.tex. Input is JSON on stdin with `logical_registers` and
optional `pc` (default25), or `physical_registers` using the HAZ allocation.
Physical marker, path, padding, and complete-tape checks are caller duties.
"""
from functools import lru_cache
from math import isqrt
import json, sys

PHYSICAL=[6,2,0,3,4,7,8,5,1]
def decode(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b

@lru_cache(None)
def formula(n):
    if not isinstance(n,int) or n<0:raise ValueError('Formula code must be a natural number')
    if n==0:return {'value':True,'rule':'truth-zero'}
    a,b=decode(n//4);tag=n%4
    if tag==1 and a==b:return {'value':False,'rule':'finite-bit-irreflexivity','label':a}
    if tag==3 and a==b:return {'value':True,'rule':'equality-reflexivity','label':a}
    if tag in (1,3):return {'value':None,'rule':'unrecognized-atom'}
    if tag==2:
        ca=formula(a)
        if ca['value'] is not None:return {'value':ca['value'],'rule':'universal-constant','body':a,'binder':b,'premise':ca}
        return {'value':None,'rule':'unrecognized-universal'}
    if a==b:return {'value':True,'rule':'implication-identity','formula':a}
    ca,cb=formula(a),formula(b)
    if ca['value'] is False:return {'value':True,'rule':'false-antecedent','antecedent':a,'consequent':b,'premise':ca}
    if cb['value'] is True:return {'value':True,'rule':'true-consequent','antecedent':a,'consequent':b,'premise':cb}
    if ca['value'] is True and cb['value'] is False:return {'value':False,'rule':'true-implies-false','antecedent':a,'consequent':b,'premises':[ca,cb]}
    return {'value':None,'rule':'unrecognized-implication'}

def stack(n):
    entries=[]
    while n:
        a,b=decode(n)
        cert=formula(a)
        entries.append({'code':a,'certificate':cert})
        if cert['value'] is not True:return {'accepted':False,'entries':entries}
        assert b<n
        n=b
    return {'accepted':True,'entries':entries,'padding':'truth-zero'}

def certify(registers,pc=25):
    if len(registers)!=9 or any(not isinstance(x,int) or x<0 for x in registers):raise ValueError('Exactly nine natural registers required')
    t,h,w=formula(registers[1]),formula(registers[5]),stack(registers[2])
    return {'accepted':25<=pc<=44 and t['value'] is True and h['value'] is True and w['accepted'],
            'pc':pc,'logical_registers':registers,'top':t,'cache':h,'stack':w,
            'scope':'PA-proof-template seed; requires valid complete runtime frame and exact source binding'}

if __name__=='__main__':
    obj=json.load(sys.stdin)
    if 'logical_registers' in obj:r=obj['logical_registers']
    else:r=[obj['physical_registers'][j] for j in PHYSICAL]
    print(json.dumps(certify(r,obj.get('pc',25)),indent=2))
