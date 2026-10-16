"""Total formula codings with a unique genuine Bottom and no extra residue.

The supported moduli are3 (equality-free) and4 (with logical equality).
Truth0; Bottom1; Imp=mP; All=mP+2; Rel=mP+m+1; Eq=4P+3.
The raw syntax collision Imp(Truth,Truth)=Truth at code0 is intentional.
"""
from functools import cache
from math import isqrt


def pair(a,b):
    return (a+b)*(a+b+1)//2+b


def unpair(n):
    diagonal=(isqrt(8*n+1)-1)//2
    b=n-diagonal*(diagonal+1)//2
    return diagonal-b,b


def codec(modulus):
    if modulus not in (3,4):raise ValueError('Supported formula moduli are3 and4')
    @cache
    def decode(n):
        if n==0:return('truth',)
        if n==1:return('bottom',)
        quotient,tag=divmod(n,modulus)
        if tag==1:
            a,b=unpair(quotient-1)
            return('rel',a,b)
        a,b=unpair(quotient)
        if tag==0:return('imp',decode(a),decode(b))
        if tag==2:return('all',a,decode(b))
        return('eq',a,b)
    def encode(f):
        kind,*args=f
        if kind=='truth':return 0
        if kind=='bottom':return 1
        a,b=args
        if kind=='rel':return modulus*pair(a,b)+modulus+1
        if kind=='eq':
            if modulus!=4:raise ValueError('Equality is absent from the3-residue codec')
            return modulus*pair(a,b)+3
        if kind=='all':return modulus*pair(a,encode(b))+2
        return modulus*pair(encode(a),encode(b))
    def labels(f):
        kind,*args=f
        if not args:return set()
        a,b=args
        if kind in ('rel','eq'):return{a,b}
        if kind=='all':return{a}|labels(b)
        return labels(a)|labels(b)
    return decode,encode,labels


def audit(bound=100000):
    results=[]
    for modulus in (3,4):
        decode,encode,labels=codec(modulus)
        for n in range(bound):
            f=decode(n)
            if encode(f)!=n or any(i>=n for i in labels(f)):
                raise AssertionError((modulus,n,f))
        assert decode(1)==('bottom',)
        assert decode(modulus+1)==('rel',0,0)
        assert decode(encode(('imp',('truth',),('truth',))))==('truth',)
        results.append(dict(modulus=modulus,numeric_codes=bound,
            exact_numeric_roundtrip=True,strict_variable_label_bound=True,
            unique_Bottom_code=1,Rel00_code=modulus+1,
            truth_collision_explicit=True))
    return results
