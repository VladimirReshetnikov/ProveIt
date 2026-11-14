#!/usr/bin/env python3
"""Exact polynomial verification for the lower-first frozen positive emitter.

Uses only exact rational arithmetic, including a complete coefficient array.
No polynomial fitting or numerical approximation is used.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path
from frozen_positive_emitter import frozen, original, require


def const(n): return (F(n),)
def add(*ps):
    out=[F(0)]*max(map(len,ps))
    for p in ps:
        for i,a in enumerate(p): out[i]+=a
    while len(out)>1 and out[-1]==0: out.pop()
    return tuple(out)
def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): out[i+j]+=a*b
    return tuple(out)
def scale(a,p): return tuple(a*x for x in p)
def tri(p): return scale(F(1,2),mul(p,add(p,const(1))))
def evaluate(p,n):
    out=F(0)
    for a in reversed(p): out=out*n+a
    return out


def polys(radix=3,reordered=True,dynamic_guard=False):
    zero=const(0); n=(F(0),F(1))
    dyadic=radix in ('dyadic','dyadic_vfirst')
    r=4 if dyadic else radix
    atom_factor=2 if dyadic else radix
    imp_tag=3 if dyadic else 2
    # These factored operations independently reconstruct the displayed program.
    R=lambda a,b: scale(atom_factor,add(tri(add(a,b)),b))
    A=lambda a,b: add(scale(r,add(tri(add(a,b)),a if radix=='dyadic' else b)),const(1))
    I=lambda a,b: add(scale(r,add(tri(add(a,b)),b)),const(imp_tag))
    guard=(A(n,I(R(n,const(1)),R(n,zero))) if dynamic_guard else
           A(const(2),I(R(const(2),const(1)),R(const(2),zero))))
    e=R(const(1),n)
    k=I(add(e,n),zero)
    u=A(const(1),add(k,scale(r,n)))
    j=add(k,scale(r,e))
    h=I(guard,j)
    v=A(const(1),h)
    first,second=(v,u) if reordered else (u,v)
    neg=I(second,zero)
    body=I(first,neg)
    quantified=A(n,body)
    output=I(quantified,zero)
    return {'e':e,'k':k,'u':u,'j':j,'h':h,'v':v,'neg':neg,
            'body':body,'quantified':quantified,'output':output}


def suite():
    results={}
    for radix in (3,4,'dyadic','dyadic_vfirst'):
        row={}
        for label,reordered,dynamic_guard in (('original_14',False,True),
                  ('upper_first',False,False),('lower_first',True,False)):
            stages=polys(radix,reordered,dynamic_guard)
            p=stages['output']
            degree=512 if dynamic_guard else (128 if reordered else 256)
            if radix in ('dyadic','dyadic_vfirst'):
                exponent=511 if dynamic_guard else (71 if reordered else 127)
                expected=F(2)**exponent
                leading_form=f'2^{exponent}'
                log2_form=f'{degree} log2(n) + {exponent} + O(1/n)'
            else:
                extra=256 if dynamic_guard else (8 if reordered else 0)
                expected=F(radix,2)**(degree-1)*F(2)**extra
                leading_form=f'2^{extra} * ({radix}/2)^{degree-1}'
                log2_form=f'{degree} log2(n) + {extra} + {degree-1} log2({radix}/2) + O(1/n)'
            require(len(p)-1==degree,'wrong degree')
            require(p[-1]==expected,'wrong leading coefficient')
            for n in list(range(16))+[1000,2**32-1,2**64,2**127+19]:
                value=evaluate(p,n)
                require(value.denominator==1,'nonintegral sample')
                reference=original(n,radix)[0] if dynamic_guard else frozen(n,radix,reordered=reordered)[0]
                require(value.numerator==reference,
                        'polynomial/integer program mismatch')
            raw='\n'.join(str(v.numerator)+'/'+str(v.denominator) for v in p).encode('ascii')
            row[label]={
                'degree':degree,'leading_coefficient':str(p[-1]),
                'leading_factor_form':leading_form,
                'coefficient_count':len(p),'nonzero_coefficients':sum(bool(x) for x in p),
                'coefficient_array_sha256':hashlib.sha256(raw).hexdigest(),
                'all_coefficients_nonnegative':all(x>=0 for x in p),
                'all_coefficients_integral':all(x.denominator==1 for x in p),
                'stage_degrees':{name:len(poly)-1 for name,poly in stages.items()},
                'asymptotic_log2':log2_form,
                'comparisons':20,
            }
        results[str(radix)]=row
    return {'status':'passed','arithmetic':'exact full Fraction coefficient arrays',
            'results':results,'scope':'specified code growth only; not a TM-state count'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(suite(),sort_keys=True,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
