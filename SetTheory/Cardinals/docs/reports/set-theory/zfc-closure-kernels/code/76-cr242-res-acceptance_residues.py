#!/usr/bin/env python3
"""Exact arithmetic witnesses for the residue acceptance theorem.

This checks arithmetic identities and finite residue coverage. Derivability of
the witness families and the unbounded acceptance theorem are ordinary proofs
in acceptance_residues.tex, not conclusions of this script.
"""
from pathlib import Path
import json

def triangular(x): return x*(x+1)//2
def pair(x,y): return triangular(x+y)+y
def imp(a,b): return 4*pair(a,b)
def all_(i,b): return 4*pair(i,b)+2
def eq(i,j): return 4*pair(i,j)+3
def accepted(n):return n%2==1 and n%16!=3

def one(k):
    modulus=1<<k
    inverse={triangular(a)%modulus:a for a in range(modulus)}
    assert len(inverse)==modulus
    witnesses={}
    for a in range(modulus):
        for family,n in [('imp_to_truth',imp(a,0)),('all_truth',all_(a,0)),('equality_refl',eq(a,a))]:
            assert not accepted(n)
            witnesses.setdefault(n%modulus,dict(family=family,parameter=a,code=n))
    # A safe congruence class must exclude all witnesses. The theory proof
    # establishes that the remaining classes are indeed safe.
    safe=sorted(set(range(modulus))-witnesses.keys())
    expected=([r for r in range(modulus) if accepted(r)] if k>=4
              else [] if k<=1 else [1] if k==2 else [1,5,7])
    assert safe==expected
    return dict(exponent=k,modulus=modulus,safe_residues=safe,
                safe_count=len(safe),theorem_witness_count=len(witnesses),
                witnesses={str(r):w for r,w in sorted(witnesses.items())})

def main():
    records=[one(k) for k in range(11)]
    for a in range(4096):
        assert imp(a,0)==4*triangular(a)
        assert all_(a,0)==4*triangular(a)+2
        assert eq(a,a)==16*triangular(a)+3
    pairs=0
    for i in range(256):
        for j in range(256):
            h=eq(i,j)
            if accepted(h):assert i!=j
            pairs+=1
    result=dict(status='PASS',scope='Finite arithmetic identities/residue witnesses, not a formal calculus proof or a TM cost.',
                identity_parameters=4096,equality_pairs=pairs,records=records)
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'}|{'coverage':[{k:v for k,v in r.items() if k not in ('witnesses','safe_residues')} for r in records]},indent=2))

if __name__=='__main__':main()
