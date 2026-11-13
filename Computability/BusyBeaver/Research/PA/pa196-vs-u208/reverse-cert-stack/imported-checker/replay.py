#!/usr/bin/env python3
"""Finite controls for the imported PA196 checker's certificate constructors.

The row evaluator implements the imported numeric tag/payload rules. Instead
of materializing their full HFS tables, it asks for individual entries by
bounded recursion on fuel, using CheckerRows.rows_nth. It is an ordinary-Python
check of examples, not a PA proof or a nonstandard-model certificate.
"""
from functools import lru_cache
import hashlib
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3] / 'jamesyc-upstream' / 'pa196'
PINS = {
    'PA196/Arithmetic/Checker.lean': '7313a9be8557d2aa5b89421f3ce9e3ac01ce4155ea57f775536d10eb382fecbc',
    'PA196/Arithmetic/CheckerRows.lean': 'cf46506a40263feeacb5ce2028e3ad48e9a6fe75aed8aa4c3dca4a455e44c929',
    'M6PA/Scheduler/SourceCantorDecodeInvariant.lean': '213057c1d734e51d16daed15cc5fe2e7dfe9f2464b8642943d1af2528fca99db',
    'PA196/Arithmetic/CheckerRule.lean': 'ec870e1bc5456af958e4638c60116bc07d7f69638ee3e9c3195aadb63d31fcf1',
    'PA196/Arithmetic/Certificates/Leaves.lean': '3e9eb8733107a961f96c1d0db89c2fefc1abd049a25f143d45879d2faa58a0e3',
    'PA196/Arithmetic/Certificates/MPGen.lean': 'dfef479620eb954ac595dea3090d61238e21569d377a7a7d87e9be2580f3c775',
    'PA196/Commands/Code.lean': '261d6536ae909f8c83fe792ed7640b465021698bc792bad1049de25bccc5410b',
    'PA196/Commands/Store.lean': 'eb29647751302d4449302254842942792e115f834ffecdf51023c30ed00615e3',
    'PA196/Arithmetic/HeadGraphs.lean': '95998688eb29f0cdc900f194e220637b0b645351c3cbc1972532533a355aacbd',
}

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def pair(a, b):
    s = a+b
    return s*(s+1)//2+b

def decode(w):
    s = (isqrt(8*w+1)-1)//2
    b = w-s*(s+1)//2
    return s-b, b

def pack(*xs):
    v = 0
    for x in reversed(xs):
        v = pair(x,v)
    return v

def unpack(v, n):
    out=[]
    for _ in range(n):
        a,v=decode(v)
        out.append(a)
    return (*out,v)

def I(a,b): return 4*pair(a,b)
def M(a,b): return 4*pair(a,b)+1
def U(a,b): return 4*pair(b,a)+2
def E(a,b): return 4*pair(a,b)+3
def neg(a): return I(a,1)
def conj(a,b): return neg(I(a,neg(b)))
def ex(a,b): return neg(U(a,neg(b)))
def head1(d,h): return I(ex(d,U(d,h)),h)
def head2(d,a,h): return I(U(d,U(a,h)),U(a,U(d,h)))
def head3(d,a,h): return I(M(h,d),I(E(h,a),M(a,d)))
def head4(d,a,h): return I(E(h,d),I(M(a,h),M(a,d)))
def head5(d,h): return ex(d,E(h,d))
def head6(d,a,h): return I(U(d,a),I(U(d,I(a,h)),U(d,h)))
def rho8(a,b,c,u): return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def bundle(a,b,c):
    eqvac=I(E(a,b),U(c,E(a,b)))
    memvac=I(M(a,b),U(c,M(a,b)))
    point=I(c,M(c,b))
    sep=U(b,conj(I(M(a,b),point),I(M(c,b),c)))
    return neg(I(eqvac,I(memvac,U(c,I(sep,neg(point))))))

def leaf(tag,*args): return pair(1,pair(tag,pack(*args)))
def gen(v,child):
    fuel,tree=decode(child)
    return pair(fuel+1,pair(1,pack(v,tree)))
def mp(b,minor,major):
    fm,tm=decode(minor); fj,tj=decode(major)
    return pair(fm+fj+1,pair(0,pack(b,tm,tj)))

@lru_cache(maxsize=None)
def entry(fuel, bound, tree):
    if not fuel or tree>bound:
        return 0
    tag,payload=decode(tree)
    arities={0:3,1:2,2:2,3:3,4:3,5:3,6:2,7:3,8:4,9:3}
    if tag not in arities:
        return 0
    args=unpack(payload,arities[tag]); tail=args[-1]; args=args[:-1]
    if tail:
        return 0
    if tag==0:
        b,p,q=args
        minor=entry(fuel-1,bound,p); major=entry(fuel-1,bound,q)
        return b+1 if minor and major and major==I(minor-1,b)+1 else 0
    if tag==1:
        v,p=args
        minor=entry(fuel-1,bound,p)
        return U(v,minor-1)+1 if minor else 0
    if tag==2: value=head1(*args)
    elif tag==3: value=head2(*args)
    elif tag==4: value=head3(*args)
    elif tag==5: value=head4(*args)
    elif tag==6: value=head5(*args)
    elif tag==7: value=head6(*args)
    elif tag==8:
        a,b,c,u=args
        if u>a: return 0
        value=rho8(*args)
    else:
        a,b,c=args
        if c==a or c==b: return 0
        value=bundle(*args)
    return value+1

def verify(code):
    fuel,tree=decode(code)
    return entry(fuel,tree,tree)

def ax_heads(D,H,A,d,h):
    return [head6(D,A,H),head5(D,H),head4(H,D,A),head3(H,D,A),
            head2(D,A,H),head1(D,H),rho8(D,A,H,d),U(d,h)]

def ax_proofs(D,H,A,d,ph):
    return [leaf(7,D,A,H),leaf(6,D,H),leaf(5,H,D,A),leaf(4,H,D,A),
            leaf(3,D,A,H),leaf(2,D,H),leaf(8,D,A,H,d),gen(d,ph)]

def main():
    for p,h in PINS.items():
        need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'source hash mismatch: '+p)
    truth=leaf(8,0,0,0,0)
    need(truth==739 and decode(truth)==(1,36) and decode(36)==(8,0),'truth code differs')
    need(verify(truth)==1,'truth rejected')
    need(verify(pair(0,36))==0,'zero fuel must reject')
    need(verify(leaf(8,0,0,0,1))==0,'rho8 guard was not enforced')
    need(verify(leaf(9,0,1,0))==0,'bundle guard was not enforced')
    proof=gen(0,truth); need(verify(proof)==U(0,0)+1,'GEN mismatch')
    proof=mp(0,truth,truth);need(verify(proof)==1,'MP at I(0,0)=0 mismatch')
    need(verify(mp(1,truth,truth))==0,'MP implication mismatch accepted')
    results=[]
    for D,H,A,d in [(0,0,0,0),(0,0,1,0),(3,2,1,1),(3,2,2,1),(3,2,3,1)]:
        heads=ax_heads(D,H,A,d,0); proofs=ax_proofs(D,H,A,d,truth)
        need([verify(p) for p in proofs]==[h+1 for h in heads],'AX head ordering mismatch')
        pt=truth if A==H or A==D else leaf(9,H,D,A)
        expected=0 if A==H or A==D else bundle(H,D,A)
        need(verify(pt)==expected+1,'AX gate mismatch')
        results.append({'D':D,'H':H,'A':A,'d':d,'head_bit_lengths':[x.bit_length() for x in heads],
                        'gate_is_guarded_truth':A==H or A==D,'gate_bit_length':expected.bit_length()})
    # Check literal numeric underflow with a nonzero ghost certificate stack.
    ghost=pair(truth,0); need(decode(0)==(0,0) and ghost!=0 and verify(truth)==1,'underflow control')
    out={'source_pins':PINS,'truth_certificate':truth,'truth_tree':36,'truth_checker_result':verify(truth),
         'gen_zero_truth_checker_result':verify(gen(0,truth)),
         'mp_truth_truth_checker_result':verify(mp(0,truth,truth)),
         'negative_controls':['zero fuel','rho8 domination','bundle guard','MP implication mismatch'],
         'ax_controls':results,'scope':'Finite exact numeric examples; targeted entries use CheckerRows.rows_nth. Not a proof in PA.'}
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
