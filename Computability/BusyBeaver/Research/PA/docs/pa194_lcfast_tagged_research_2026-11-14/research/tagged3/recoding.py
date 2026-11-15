#!/usr/bin/env python3
"""Exact recoding for a three-residue numerical calculus with tagged atom operand.

This script checks finite instances of the constructor identities proved in
recoding.tex.  It is not an end-to-end proof assistant certificate.
All natural numbers are admissible codes.  Formula codes AND variable labels
are recoded by the same inverse pair of primitive-recursive permutations.
"""
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json

def pair(a,b):
    return (a+b)*(a+b+1)//2+b

def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b

class Constructors:
    def __init__(self,tagged=False): self.tagged=tagged
    def I(self,a,b): return (3 if self.tagged else 4)*pair(a,b)
    def M(self,a,b):
        return 3*pair(a,2*b)+1 if self.tagged else 4*pair(a,b)+1
    def E(self,a,b):
        return 3*pair(a,2*b+1)+1 if self.tagged else 4*pair(a,b)+3
    def U(self,a,b): return self.I(b,a)+2
    def N(self,a): return self.I(a,1)
    def And(self,a,b): return self.N(self.I(a,self.N(b)))
    def Exists(self,a,b): return self.N(self.U(a,self.N(b)))
    def Gamma(self,a): return self.I(a,self.U(a,a))
    def rho(self,d,a,h,u):
        return self.I(self.I(self.I(h,u),d),self.I(self.I(d,h),self.I(a,h)))
    def heads(self,d,a,h):
        return [
          self.I(self.Exists(d,self.U(d,h)),h),
          self.I(self.U(d,self.U(a,h)),self.U(a,self.U(d,h))),
          self.I(self.M(h,d),self.I(self.E(h,a),self.M(a,d))),
          self.I(self.E(h,d),self.I(self.M(a,h),self.M(a,d))),
          self.Exists(d,self.E(h,d)),
          self.I(self.U(d,a),self.I(self.U(d,self.I(a,h)),self.U(d,h))),
        ]
    def head6q(self,d,a,h):
        return self.I(self.U(d,self.I(a,h)),self.I(self.U(d,a),self.U(d,h)))
    def gate(self,a,b,c):
        v=self.I(self.M(a,b),self.U(c,self.M(a,b)))
        p=self.I(c,self.M(c,b))
        s=self.U(b,self.And(self.I(self.M(a,b),p),self.I(self.M(c,b),c)))
        q=self.U(c,self.I(s,self.N(p)))
        return self.N(self.I(v,q)) if c!=a and c!=b else 0

C4=Constructors(False)
C3=Constructors(True)

@lru_cache(None)
def forward(n):
    if n==0:return 0
    a,b=unpair(n//4)
    tag=n%4
    if tag==0:return C3.I(forward(a),forward(b))
    if tag==1:return C3.M(forward(a),forward(b))
    if tag==2:return C3.U(forward(b),forward(a))
    return C3.E(forward(a),forward(b))

@lru_cache(None)
def backward(n):
    if n==0:return 0
    a,b=unpair(n//3)
    tag=n%3
    if tag==0:return C4.I(backward(a),backward(b))
    if tag==2:return C4.U(backward(b),backward(a))
    if b%2==0:return C4.M(backward(a),backward(b//2))
    return C4.E(backward(a),backward(b//2))

def main():
    tested=10000
    for n in range(tested):
        assert backward(forward(n))==n
        assert forward(backward(n))==n
    counts={'inverse_values_each_direction':tested,'constructor_cases':0,
            'six_head_cases':0,'q_head_cases':0,'diagonal_cases':0,'gate_cases':0,
            'rho_expression_cases':0}
    for a in range(24):
        for b in range(24):
            for name in ['I','M','U','E']:
                assert forward(getattr(C4,name)(a,b))==getattr(C3,name)(forward(a),forward(b))
                assert backward(getattr(C3,name)(a,b))==getattr(C4,name)(backward(a),backward(b))
                counts['constructor_cases']+=2
    for d in range(4):
        for a in range(4):
            for h in range(4):
                assert [forward(x) for x in C4.heads(d,a,h)]==C3.heads(forward(d),forward(a),forward(h))
                assert [backward(x) for x in C3.heads(d,a,h)]==C4.heads(backward(d),backward(a),backward(h))
                counts['six_head_cases']+=12
                assert forward(C4.head6q(d,a,h))==C3.head6q(forward(d),forward(a),forward(h))
                assert backward(C3.head6q(d,a,h))==C4.head6q(backward(d),backward(a),backward(h))
                counts['q_head_cases']+=2
                assert forward(C4.gate(d,a,h))==C3.gate(forward(d),forward(a),forward(h))
                assert backward(C3.gate(d,a,h))==C4.gate(backward(d),backward(a),backward(h))
                counts['gate_cases']+=2
                for u in range(4):
                    assert forward(C4.rho(d,a,h,u))==C3.rho(forward(d),forward(a),forward(h),forward(u))
                    assert backward(C3.rho(d,a,h,u))==C4.rho(backward(d),backward(a),backward(h),backward(u))
                    counts['rho_expression_cases']+=2
    for a in range(24):
        assert forward(C4.Gamma(a))==C3.Gamma(forward(a))
        assert backward(C3.Gamma(a))==C4.Gamma(backward(a))
        counts['diagonal_cases']+=2
    receipt={'status':'PASS: finite exact recoding checks',
      'scope':'Finite checks support recoding.tex; no proof-assistant endpoint is asserted.',
      'constructors':{'I':'3*p(a,b)','U':'3*p(body,binder)+2','M':'3*p(a,2*b)+1','E':'3*p(a,2*b+1)+1'},
      'counts':counts,
      'first_24_forward':[forward(n) for n in range(24)],
      'first_24_backward':[backward(n) for n in range(24)],
      'not_monotone_example':{'old_u':3,'old_D':4,'forward_u':forward(3),'forward_D':forward(4)},
      'rho_guard_policy':'Do NOT preserve u<=D by recoding; expand translated rho leaf with unrestricted rho8All.',
      'fixed_zero':forward(0)==backward(0)==0,
      'fixed_one':forward(1)==backward(1)==1}
    Path(__file__).with_name('recoding_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
