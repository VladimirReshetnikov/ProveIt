#!/usr/bin/env python3
"""Finite independent checks of the boundary and translated Boolean cover."""
from itertools import product
import json
from pathlib import Path

def digits(n,b,k):
    return [(n//b**i)%b for i in range(k)]

boundary_cases=0
for B in range(2,7):
  for m in range(1,4):
    for ds in product(range(B),repeat=m):
      if not ds[-1]: continue
      D=sum(x*B**i for i,x in enumerate(ds)); M=B**m
      for C in range(2*M):
        assert ((C-D)%M==0)==(digits(C,B,m)==list(ds))
        if (C-D)%M==0: assert (C-D)//M>=0
        boundary_cases+=1

# A small valid controller: d=1, lambda=3, B=2, N=27, T=9, k=2.
# Its orbit is precisely 1+3z modulo 27, and the finite prefix is displaced.
B=2; lam=3; N=27; T=9; k=2; C0=3
orbit={((pow(B,k*j,N)-1)//C0):j for j in range(T)}
assert set(orbit)==set(range(T))
coverage_cases=0
for prefix in range(1,5):
  a=prefix+1
  for r in range(N):
    rr=r*pow(pow(B,a,N),-1,N)%N
    eps=next(e for e in (0,1) if (rr-e*B)%lam)
    target=(rr-eps*B)%N; b=target%C0
    u=((target-b)//C0)%T
    z0=((u-b*(b-1)//2)*pow(b,-1,T))%T
    indices=[a+k*orbit[(z0+i)%T] for i in range(b)]
    if eps: indices.append(a+1)
    assert len(indices)==len(set(indices))
    assert min(indices)>=prefix and max(indices)<N
    assert sum(pow(B,j,N) for j in indices)%N==r
    coverage_cases+=1
# Exhaustively check finite initializer strips: each tile has left/right phase,
# output tape symbol and a head flag. The fixed suffix before Start is the input.
Gamma=(0,1)
tiles=[('L','L',0,0,'blankL'),('R','R',0,0,'blankR')]
tiles += [('L','D',a,1,'head'+str(a)) for a in Gamma]
tiles += [('D','D',a,0,'data'+str(a)) for a in Gamma]
tiles += [('D','R',0,0,'Start')]
initializer_cases=0
for word in ((0,),(1,),(0,1),(1,0,1)):
  expected=['head'+str(word[0])]+['data'+str(a) for a in word[1:]]+['Start']
  for width in range(len(expected),9):
    paths=[([], 'L')]
    for _ in range(width):
      paths=[(seq+[t],t[1]) for seq,state in paths for t in tiles if t[0]==state]
    for seq,state in paths:
      if state!='R': continue
      names=[t[4] for t in seq]
      mark=names.index('Start')
      first=mark-len(word)
      if first<0 or names[first:mark+1]!=expected: continue
      assert names[:first]==['blankL']*first
      assert names[mark+1:]==['blankR']*(width-mark-1)
      assert sum(t[3] for t in seq)==1
      assert tuple(t[2] for t in seq[first:mark])==word
      initializer_cases+=1

out={'initializer_strip_cases':initializer_cases,'boundary_cases' :boundary_cases,'translated_cover_cases':coverage_cases,
     'scope':'Finite identity checks only; no universal machine or Con(ZFC) endpoint asserted.'}
Path(__file__).with_name('AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
