#!/usr/bin/env python3
"""Emit the exact 199-item distributed-separation AX word.

The symbolic constructors encode PA196's numerical convention, including
transposed universal quantifiers. This file produces a register-macro word,
not a Turing-machine state-count certificate.

The construction is derived from jamesyc/BusyBeaver's PA196 program and the
formula emitter in ProveIt's incoming pa_tm_research_2026-11-13 archive.
Upstream source identification and notices accompany this file.
"""
import json
from pathlib import Path

INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)
VARS = {'D': 'node55', 'H': 'node58', 'A': 'node70'}
PREFIX = ['node58','node55','node65',INC,INC,'node72','node58','node55',
          'node65','node75','node55','node58','node65','node70','node58',
          'node65','node65','node65']
SUFFIX = ['node142','node150',BREAK]
HEAD_ORDER = [0,5,1,2,3,4]

def I(a,b):return (0,a,b)
def M(a,b):return (1,a,b)
def U(a,b):return (2,b,a)
def E(a,b):return (3,a,b)
def N(a):return I(a,'1')
def conjunction(a,b):return N(I(a,N(b)))
def exists(a,b):return N(U(a,N(b)))

def emit(f):
    if isinstance(f,str):return ['node49',INC]if f=='1'else[VARS[f]]
    tag,a,b=f
    return emit(a)+emit(b)+['node65']+[INC]*tag

def heads(exchange_distribution=False):
    d,h,a='DHA'
    out=[I(exists(d,U(d,h)),h),
         I(U(d,U(a,h)),U(a,U(d,h))),
         I(M(h,d),I(E(h,a),M(a,d))),
         I(E(h,d),I(M(a,h),M(a,d))),
         exists(d,E(h,d)),
         I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
    if exchange_distribution:
        _,x,(_,y,z)=out[5]
        out[5]=I(y,I(x,z))
    return out

def gate(distributed=True):
    a,b,c='HDA'
    delta=I(E(a,b),U(c,E(a,b)))
    vacuity=I(M(a,b),U(c,M(a,b)))
    point=I(c,M(c,b))
    lower=I(M(a,b),point)
    upper=I(M(c,b),c)
    if distributed:
        q=U(c,I(U(b,lower),I(U(b,upper),N(point))))
    else:
        q=U(c,I(U(b,conjunction(lower,upper)),N(point)))
    return N(I(delta,I(vacuity,q)))

def candidate_word():
    hh=heads(True)
    return PREFIX+sum((emit(hh[j])for j in HEAD_ORDER),[])+emit(gate(True))+SUFFIX

def baseline_word():
    return PREFIX+sum(map(emit,heads()),[])+emit(gate(False))+SUFFIX

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path)
    args=ap.parse_args();s=json.dumps(candidate_word(),indent=2)+'\n'
    if args.out:args.out.write_text(s)
    else:print(s,end='')
