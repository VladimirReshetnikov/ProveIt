#!/usr/bin/env python3
"""Exact, dependency-free equivalence of the repository's two S6 candidates.

The program proves their difference is a combination of TWO CONVERGENT
SHUFFLES. It does not prove either candidate. All coefficients are rational.
"""
from fractions import Fraction as Q
from math import comb
import json

def add(a,b,scale=Q(1)):
    out=dict(a)
    for k,v in b.items():
        out[k]=out.get(k,Q(0))+scale*v
        if not out[k]:del out[k]
    return out

def shuffle_coefficients(p,q):
    """The two possible orders of the last nonzero letters."""
    w=p+q;out={}
    for j in range(1,p+1):
        out=add(out,{f'g{w-j}{j}':Q(comb(w-j-1,q-1))})
    for j in range(1,q+1):
        out=add(out,{f'g{w-j}{j}':Q(comb(w-j-1,p-1))})
    return out

def main():
    E25=add(shuffle_coefficients(2,5),
            {'pi7':Q(-5,73728),'Gzeta5':Q(-15,512)},-1)
    E34=add(shuffle_coefficients(3,4),
            {'pi7':Q(-7,368640),'beta4zeta3':Q(-3,32)},-1)
    old={'S6':Q(1),'g61':Q(-722,527),'g43':Q(-40,527),
         'g25':Q(128,155),'pi7':Q(-15191,28569600),
         'Gzeta5':Q(3,124),'beta4zeta3':Q(2373,10540),'beta6L':Q(2)}
    new={'S6':Q(1),'g61':Q(12334,527),'g52':Q(384,31),
         'g43':Q(2136,527),'pi7':Q(-3179,5713920),
         'beta4zeta3':Q(801,2108),'beta6L':Q(2)}
    residual=add(add(old,new,-1),add(E25,E34,-2),Q(-128,155))
    assert not residual
    # This second direct substitution also verifies the displayed elimination.
    g25={'g61':Q(30),'g52':Q(15),'g43':Q(5),
         'pi7':Q(-11,368640),'Gzeta5':Q(-15,512),
         'beta4zeta3':Q(3,16)}
    eliminated=old.copy();c=eliminated.pop('g25')
    eliminated=add(eliminated,g25,c)
    assert eliminated==new
    result={'verified':True,'arithmetic':'exact rational',
            'meaning':'equivalence of two conjectures, not a proof of either',
            'identity':'R_old - R_Cayley = (128/155)(E25 - 2 E34)',
            'convergent_shuffle_rows':2,'residual_terms':0,
            'g25_elimination':{k:str(v) for k,v in g25.items()},
            'normalized_cayley_residual':{k:str(v) for k,v in new.items()}}
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
