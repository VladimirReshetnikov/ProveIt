#!/usr/bin/env python3
"""Exact universal coefficient check for the shipped five-root norm routine.

The expected polynomial is built independently by successive translations
F(x+sqrt(a))*F(x-sqrt(a)), using binomial coefficients and integer sparse
polynomial arithmetic. The implementation under examination is imported
only to obtain the actual polynomial. No modular sampling is used here.
Standard library only.
"""
from pathlib import Path
from math import comb
import argparse, hashlib, importlib.util, json, time

BITS=6
MASK=(1<<BITS)-1
NAMES=('x','a','b','c','d','cn','delta')


class Polynomial:
    def __init__(self,terms):
        self.terms={k:v for k,v in terms.items() if v}
    @staticmethod
    def constant(n):return Polynomial({0:n})
    @staticmethod
    def variable(i):return Polynomial({1<<(BITS*i):1})
    @staticmethod
    def coerce(x):return x if isinstance(x,Polynomial) else Polynomial.constant(x)
    def __add__(self,other):
        other=self.coerce(other);d=dict(self.terms)
        for k,v in other.terms.items():
            w=d.get(k,0)+v
            if w:d[k]=w
            elif k in d:del d[k]
        return Polynomial(d)
    __radd__=__add__
    def __neg__(self):return Polynomial({k:-v for k,v in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other)
        d={}
        for i,a in self.terms.items():
            for j,b in other.terms.items():
                k=i+j;d[k]=d.get(k,0)+a*b
        return Polynomial(d)
    __rmul__=__mul__
    def square(self):
        entries=list(self.terms.items());d={}
        for i,(k,a) in enumerate(entries):
            d[2*k]=d.get(2*k,0)+a*a
            for l,b in entries[i+1:]:
                key=k+l;d[key]=d.get(key,0)+2*a*b
        return Polynomial(d)


def next_radical_norm(poly,radicand_index):
    even={};odd={};radix=1<<(BITS*radicand_index)
    for key,coefficient in poly.terms.items():
        n=key&MASK
        rest=key-n
        for j in range(n+1):
            out=odd if j&1 else even
            target=rest+(n-j)+(j//2)*radix
            out[target]=out.get(target,0)+coefficient*comb(n,j)
    return Polynomial(even).square()-Polynomial.variable(radicand_index)*Polynomial(odd).square()


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--norm-source',type=Path,
        default=Path(__file__).resolve().parent/'norm5.py')
    ap.add_argument('--receipt',type=Path,required=True);args=ap.parse_args()
    t0=time.monotonic();poly=Polynomial.variable(0);stages=[]
    for i in range(1,6):
        poly=next_radical_norm(poly,i)
        stages.append(len(poly.terms));print('Independent norm stage',i,'terms',len(poly.terms),flush=True)
    # Clear the denominator after the independent universal norm is complete.
    shifted={}
    for key,value in poly.terms.items():
        e=(key>>(5*BITS))&MASK
        if e>16:raise ValueError('radicand exponent exceeds16')
        target=key+((16-e)<<(6*BITS));shifted[target]=value
    expected=Polynomial(shifted)
    spec=importlib.util.spec_from_file_location('norm_subject',args.norm_source)
    subject=importlib.util.module_from_spec(spec);spec.loader.exec_module(subject)
    variables=[Polynomial.variable(i) for i in range(7)]
    actual=subject.cleared_norm5(*variables)
    if actual.terms!=expected.terms:
        raise ValueError('generic integer polynomial coefficients differ')
    # The packed representation is valid because every exponent is below64;
    # the natural bounds follow from the32-factor degree, and are checked.
    maxes=[max((key>>(BITS*i))&MASK for key in expected.terms) for i in range(7)]
    if maxes!=[32,16,16,16,16,16,16]:raise ValueError('generic exponent bounds')
    ordered=[[[(key>>(BITS*i))&MASK for i in range(7)],value]
             for key,value in sorted(expected.terms.items())]
    digest=hashlib.sha256(json.dumps(ordered,separators=(',',':')).encode()).hexdigest()
    receipt={'identity':'delta^16 F32(x;a,b,c,d,cn/delta)',
             'method':'Exact integer coefficients; independent successive binomial translations and conjugate products',
             'independent_stage_terms':stages,'matched_terms':len(expected.terms),
             'coordinate_order':NAMES,'maximum_individual_exponents':maxes,
             'canonical_coefficient_sha256':digest,
             'subject_sha256':hashlib.sha256(args.norm_source.read_bytes()).hexdigest(),
             'seconds':round(time.monotonic()-t0,6)}
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
