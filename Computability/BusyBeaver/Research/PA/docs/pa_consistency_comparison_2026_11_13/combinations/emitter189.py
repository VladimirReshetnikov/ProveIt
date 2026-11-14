#!/usr/bin/env python3
"""Reconstruct the combined distributed/diagonal AX word and exact source sizes.

The emitter has 189 macros, not 189 machine states. Its logical adequacy and
physical compilation have separate proof obligations; this is a source audit.
The upstream literal PA196 emitter is reconstructed as a positive control.
"""
from pathlib import Path
import argparse,json,sys,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'verification'))
import symbolic as s
INC=('inc',1);BR=('breakTo',1)
VARS={'D':'node55','H':'node58','A':'node70'}
PREFIX=['node58','node55','node65',INC,INC,'node72','node58','node55',
        'node65','node75','node55','node58','node65','node70','node58',
        'node65','node65','node65']
SUFFIX=['node142','node150',BR]

def I(a,b):return (0,a,b)
def M(a,b):return (1,a,b)
def U(a,b):return (2,b,a)
def E(a,b):return (3,a,b)
def N(a):return I(a,'1')
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
def emit(f):
 if isinstance(f,str):return ['node49',INC]if f=='1'else[VARS[f]]
 tag,a,b=f;return emit(a)+emit(b)+['node65']+[INC]*tag

def heads(exchange=False):
 d,h,a='DHA'
 out=[I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
      I(M(h,d),I(E(h,a),M(a,d))),I(E(h,d),I(M(a,h),M(a,d))),
      Ex(d,E(h,d)),I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
 if exchange:
  _,x,(_,y,z)=out[5];out[5]=I(y,I(x,z))
 return out

def gate(distributed,diagonal):
 a,b,c='HDA'
 delta=I(c,U(c,c))if diagonal else I(E(a,b),U(c,E(a,b)))
 vacuity=I(M(a,b),U(c,M(a,b)))
 point=I(c,M(c,b));lower=I(M(a,b),point);upper=I(M(c,b),c)
 body=I(U(b,lower),I(U(b,upper),N(point)))if distributed else I(U(b,And(lower,upper)),N(point))
 return N(I(delta,I(vacuity,U(c,body))))

def baseline_word():return PREFIX+sum(map(emit,heads()),[])+emit(gate(False,False))+SUFFIX

def combined_word():
 hs=heads(True)
 return PREFIX+sum((emit(hs[i])for i in (0,5,1,2,3,4)),[])+emit(gate(True,True))+SUFFIX

def shorten_negation(word):
 out=[];n=0;i=0
 while i<len(word):
  if word[i:i+3]==['node49',INC,'node65']:
   out+=['node37',INC,'node64'];i+=3;n+=1
  else:out.append(word[i]);i+=1
 return out,n

def macro_word(t):
 names=['node49','node58','node55','node70','node65','node72','node75','node142','node150']
 for name in names:
  if t==s.NODES[name]:return[name]
 if s.isleaf(t):return[t]
 return macro_word(t[0])+macro_word(t[1])

def count_sites(word):return sum(s.size(s.NODES[t])if isinstance(t,str)else 1 for t in word)+169

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args()
 old=baseline_word();assert old==macro_word(s.NODES['x67'])and len(old)==201 and count_sites(old)==3812
 new=combined_word();short,n=shorten_negation(new)
 assert len(new)==len(short)==189 and n==6
 assert count_sites(new)==3661 and count_sites(short)==3499
 out={'baseline_literal_word_equal':True,'baseline_macros':201,'baseline_sites':3812,
      'combined_macros':189,'combined_sites':3661,'combined_sites_with_mp':3638,
      'negation_replacements':6,'combined_short_negation_sites':3499,
      'combined_short_negation_sites_with_mp':3476,'head_order_zero_based':[0,5,1,2,3,4],
      'h6_antecedents_exchanged':True,'original_freshness_guard_retained':True,
      'word':new,'short_negation_word':short,
      'scope':'Exact source word and size audit; no sub196 machine or PA endpoint claimed.'}
 data=json.dumps(out,indent=2)+'\n'
 if a.output:a.output.write_text(data)
 print(data,end='')
if __name__=='__main__':main()
