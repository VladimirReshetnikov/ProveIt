#!/usr/bin/env python3
"""Finite arithmetic checks accompanying the universal recoding proof.
These checks do not replace induction in calculus_transports.tex.
"""
from functools import cache
from math import isqrt
from pathlib import Path
import json

def pair(a,b):return (a+b)*(a+b+1)//2+b

def unpair(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
 return s-b,b

@cache
def F(n):
 if n==0:return 0
 a,b=unpair(n//4);r=n%4
 assert a<n and b<n
 return 4*pair(F(a),F(b))+[0,1,3,2][r]

def main():
 for n in range(20000):assert F(F(n))==n
 for a in range(80):
  for b in range(80):
   fa,fb=F(a),F(b)
   assert F(4*pair(a,b))==4*pair(fa,fb)
   assert F(4*pair(a,b)+1)==4*pair(fa,fb)+1
   assert F(4*pair(a,b)+2)==4*pair(fa,fb)+3
   assert F(4*pair(a,b)+3)==4*pair(fa,fb)+2
 assert F(0)==0 and F(1)==1 and F(2)>F(3)
 receipt={'passed':True,'involution_inputs':20000,'constructor_pairs':6400,
  'constructor_equations':25600,'truth_false_fixed':True,
  'nonmonotonicity_witness':{'old':[2,3],'new':[F(2),F(3)]},
  'scope':'Finite supporting audit only. The all-natural theorem and proof translations are established by the separate induction proof.'}
 (Path(__file__).parent/'recoding_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
