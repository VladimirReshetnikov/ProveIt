#!/usr/bin/env python3
"""Recursively recode both variable labels and formula constructors.

This implements the exact constructor algebra bijection, not a new TM.
The finite checks are transcription controls for the proof in recoding.tex.
"""
from functools import lru_cache
from math import isqrt
import hashlib,json
from pathlib import Path

def pair(a,b):return (a+b)*(a+b+1)//2+b

def unpair(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
 return s-b,b

def enc4(tag,a,b):return 4*pair(a,b)+tag

def dec4(n):
 q,r=divmod(n,4);a,b=unpair(q);return r,a,b

def enc26(tag,a,b):
 p=pair(a,b)
 return 2*p if tag==0 else 6*p+(2*tag-1)

def dec26(n):
 if n%2==0:tag=0;p=n//2
 else:p,r=divmod(n,6);tag=(r+1)//2
 a,b=unpair(p);return tag,a,b

@lru_cache(None)
def forward(n):
 if n==0:return 0
 tag,a,b=dec4(n)
 if not(a<n and b<n):raise ValueError('old code does not descend')
 return enc26(tag,forward(a),forward(b))

@lru_cache(None)
def backward(n):
 if n==0:return 0
 tag,a,b=dec26(n)
 if not(a<n and b<n):raise ValueError('new code does not descend')
 return enc4(tag,backward(a),backward(b))

def formula_ops(enc):
 I=lambda a,b:enc(0,a,b)
 M=lambda a,b:enc(1,a,b)
 U=lambda a,b:enc(2,b,a)  # binder/body, transposed raw pair
 E=lambda a,b:enc(3,a,b)
 N=lambda a:I(a,1)
 A=lambda a,b:N(I(a,N(b)))
 def gate(a,b,c):
  dv=I(E(a,b),U(c,E(a,b)));v=I(M(a,b),U(c,M(a,b)))
  p=I(c,M(c,b));s=U(b,A(I(M(a,b),p),I(M(c,b),c)))
  q=U(c,I(s,N(p)))
  return N(I(dv,I(v,q)))
 return I,M,U,E,N,A,gate

def main():
 require=lambda ok: ok or (_ for _ in ()).throw(ValueError('transcription control failed'))
 for n in range(10000):
  require(enc4(*dec4(n))==n);require(enc26(*dec26(n))==n)
  require(backward(forward(n))==n);require(forward(backward(n))==n)
 h=0
 for tag in range(4):
  for a in range(21):
   for b in range(21):
    require(forward(enc4(tag,a,b))==enc26(tag,forward(a),forward(b)));h+=1
 old=formula_ops(enc4);new=formula_ops(enc26);gate=0
 for a in range(4):
  for b in range(4):
   for c in range(4):
    require(forward(old[-1](a,b,c))==new[-1](forward(a),forward(b),forward(c)));gate+=1
 require([forward(2),forward(3),forward(4)]==[3,5,2])
 data={'integer_roundtrips_each_direction':10000,'constructor_homomorphism_controls':h,'gate_homomorphism_controls':gate,'truth_and_false_fixed':[forward(0),forward(1)],'nonmonotonicity_example':{'old':[2,3,4],'new':[forward(2),forward(3),forward(4)]},'prefix_permutation_sha256':hashlib.sha256(json.dumps([forward(n)for n in range(10000)],separators=(',',':')).encode()).hexdigest(),'scope':'Constructor recoding only; finite transcription checks support the written proof. No literal machine or state saving is asserted.'}
 (Path(__file__).resolve().parent/'receipt.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))
if __name__=='__main__':main()
