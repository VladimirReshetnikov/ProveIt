#!/usr/bin/env python3
"""Arithmetic cross-checks for the dirty-unpair proof-code constructions.

These finite checks supplement the all-natural algebraic proof in the TeX
note. They check field parsing and counters, not the binary runtime or the
logical axiom constructors.
"""
from math import isqrt
from itertools import product
import json

def P(a,b):return (a+b)*(a+b+1)//2+b
def unP(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
 return s-b,b

def parse(packet,d,h,order,common):
 selector,pl=unP(packet);z=0
 if common:z,pl=unP(pl);d+=z
 if selector==0:
  if not common:z,pl=unP(pl);d+=z
  return {'kind':'MP','increment':z,'d':d,'h':0,'pl':pl}
 if selector in (1,2):return {'kind':'DROP' if selector==1 else 'NIP','d':d,'h':h,'pl':pl}
 U=d
 if order=='YX':y,pl=unP(pl);h+=y
 A,pl=unP(P(U,0)+pl)
 if order=='XY':y,pl=unP(pl);h+=y
 return {'kind':'AX','c':selector-3,'A':A,'B':h,'U':U,'d':0,'h':0,'pl':pl}

def prefix(R,y,order,common):
 payload=P(y,R);increment=payload if order=='XY' else R
 Q=1+P(3,P(0,payload) if common else payload)
 return P(0,P(increment,Q))

def enc(commands,d,order,common):
 if not commands:return 0
 cmd,*rest=commands;kind=cmd[0]
 nextd=d+cmd[1] if kind=='MP' else 0 if kind=='AX' else d
 R=enc(rest,nextd,order,common)
 if kind=='MP':packed=P(0,P(cmd[1],R))
 elif kind in ('DROP','NIP'):
  packed=P(1 if kind=='DROP' else 2,P(0,R)if common else R)
 else:
  _,c,A,y=cmd;assert A>=d
  payload=P(A,P(y,R))-P(d,0) if order=='XY' else P(y,P(A,R)-P(d,0))
  assert payload>=0
  packed=P(c+3,P(0,payload)if common else payload)
 return 1+packed

def main():
 prefix_checks=0;drain_checks=0;block_checks=0
 small=list(range(9));large=[2**31-1,2**64+17,10**50+1]
 cases=list(product(small,range(3),range(5),range(7)))
 cases += [(d,h,y,R)for d,h,y,R in product(large,[0,1],large,large)]
 for order,common in product(['XY','YX'],[False,True]):
  for d,h,y,R in cases:
   N=prefix(R,y,order,common);assert N>=y
   first=parse(N,d,h,order,common);assert first['kind']=='MP'
   second=parse(first['pl']-1,first['d'],first['h'],order,common)
   assert second['kind']=='AX' and second['c']==0
   assert second['A']==d and second['B']==y and second['pl']==R
   assert second['d']==second['h']==0
   prefix_checks+=1
  words=[ [('MP',1),('AX',1,1,0)],
          [('MP',7),('AX',4,11,3),('NIP',)],
          [('DROP',),('MP',5),('AX',5,5,0)],
          [('AX',4,0,9),('MP',3),('AX',2,8,1),('DROP',)] ]
  for word in words:
   d=0;pl=enc(word,d,order,common)
   for cmd in word:
    before=d;out=parse(pl-1,d,0,order,common)
    assert out['kind']==cmd[0] and out['pl']<pl
    if cmd[0]=='AX':
     assert (out['c'],out['A'],out['U'])==(cmd[1],cmd[2],before)
    d=out['d'];pl=out['pl'];block_checks+=1
   assert pl==0
 for U,n in product(range(101),repeat=2):
  A,R=unP(P(U,0)+n)
  assert R<=n and A+R<=U+n
  if U>=n:assert (A,R)==(U-n,n)
  drain_checks+=1
 return {'verified':True,'orders':['XY','YX'],'common_field_variants':[False,True],
         'uniform_prefix_checks':prefix_checks,'backward_encoding_command_checks':block_checks,
         'dirty_reader_arithmetic_checks':drain_checks,
         'scope':'Finite arithmetic parser cross-checks; universal proof is in dirty_unpair_calibration.tex.'}

if __name__=='__main__':print(json.dumps(main(),indent=2))
