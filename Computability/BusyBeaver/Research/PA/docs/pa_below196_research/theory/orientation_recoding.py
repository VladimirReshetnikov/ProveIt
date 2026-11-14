#!/usr/bin/env python3
"""Check the exact decoding/label lemmas for M/E argument transpositions.

The accompanying THEORY.md proves the all-natural claims by induction.
These finite checks test the implementation, not an internal PA endpoint.
"""
from functools import lru_cache
import json
import math
from pathlib import Path

def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(n):
    k=(math.isqrt(8*n+1)-1)//2
    b=n-k*(k+1)//2
    return k-b,b

@lru_cache(None)
def decode(n,mode):
    if n==0:return ('truth',)
    a,b=unpair(n//4)
    tag=n%4
    if tag==0:return ('imp',decode(a,mode),decode(b,mode))
    if tag==1:return ('mem',b,a) if mode&2 else ('mem',a,b)
    if tag==2:return ('all',b,decode(a,mode))
    return ('eq',b,a) if mode&1 else ('eq',a,b)

@lru_cache(None)
def recode(n,mode):
    if n==0:return 0
    a,b=unpair(n//4)
    tag=n%4
    if tag==0:a,b=recode(a,mode),recode(b,mode)
    elif tag==2:a=recode(a,mode)
    elif (tag==1 and mode&2)or(tag==3 and mode&1):a,b=b,a
    return 4*pair(a,b)+tag

def names(f):
    if f[0]=='truth':return set()
    if f[0] in ('mem','eq'):return {f[1],f[2]}
    if f[0]=='imp':return names(f[1])|names(f[2])
    return {f[1]}|names(f[2])

def free(f):
    if f[0]=='truth':return set()
    if f[0] in ('mem','eq'):return {f[1],f[2]}
    if f[0]=='imp':return free(f[1])|free(f[2])
    return free(f[2])-{f[1]}

def main():
    checked=0
    for mode in range(4):
        assert recode(0,mode)==0 and recode(1,mode)==1
        for n in range(4096):
            r=recode(n,mode)
            assert decode(r,mode)==decode(n,0)
            assert recode(r,mode)==n
            assert names(decode(r,mode))==names(decode(n,0))
            assert free(decode(r,mode))==free(decode(n,0))
            assert all(x<n for x in names(decode(n,mode)))
            assert n not in names(decode(r,mode))
            assert r not in names(decode(r,mode))
            checked+=1
    # Concrete failure of the naive gate transport's freshness guard.
    c,a,b=5,9,0
    assert c!=a and c!=b
    assert recode(c,2)==a
    result={'tested_codes_per_mode':4096,'modes':4,'cases':checked,
            'checked_properties':['decode_mode(recode_mode(n))=decode_0(n)',
                'recode_mode(recode_mode(n))=n','name and free-name preservation',
                'all labels strictly below positive code','old and new private-code freshness',
                'truth 0 and falsity 1 fixed'],
            'naive_gate_guard_counterexample':{'old_property_code':c,'a':a,'b':b,
                'membership_transposed_property_code':recode(c,2),
                'old_guard_holds':True,'naive_new_guard_holds':False},
            'proof_status':'Ordinary structural-induction lemma with finite implementation checks; alpha-renaming/padded-property proof transport and PA-internal machine equivalence are not supplied.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
