#!/usr/bin/env python3
"""Finite independent corroboration of the abstract biased-scheduler theorem.
This does not assert that any archived physical table implements the contracts.
"""
import itertools,json,math,argparse,os
if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):raise SystemExit("Disable Python optimization")
from pathlib import Path

def P(a,b):return (a+b)*(a+b+1)//2+b

def unpair(n):
 d=(math.isqrt(8*n+1)-1)//2;y=n-d*(d+1)//2
 return d-y,y

def fields(c):
 if c[0]=='S':return [0]
 if c[0]=='M':return [1,c[1]]
 return [c[1]+2,c[3],c[2]]

def fold(fs,r):
 for a in reversed(fs):r=P(a,r)
 return r

def encode(word,r):
 assert word and r>=1
 for i in range(len(word)-1,0,-1):
  r=1-int(word[i-1][0]!='S')+fold(fields(word[i]),r)
  assert r>0
 return fold(fields(word[0]),r)

def prefix(n,k):
 out=[];r=n;b=0
 for i in range(k):
  if i:
   assert r>0, ('Premature refill',i)
   r=r-1+b
  a,r=unpair(r)
  if a==0:c=('S',);b=0
  elif a==1:
   x,r=unpair(r);c=('M',x);b=1
  else:
   y,r=unpair(r);x,r=unpair(r);c=('A',a-2,x,y);b=1
  out.append(c)
 return out,r,b

def main():
 assert __debug__,'Assertions must be enabled'
 alphabet=[('S',),('M',0),('M',1),('A',0,0,0),('A',1,1,1)]
 cases=0;maxbits=0
 for size in range(1,4):
  for w in itertools.product(alphabet,repeat=size):
   w=list(w)
   for r in (1,2,3):
    K=encode(w,r)
    assert prefix(K,size)[0]==w
    for x in (0,1,2,7):
     n=P(1,P(x,P(0,1+K)))
     assert n-1==P(2,P(x+1,P(1,K)))
     assert prefix(n,size+2)[0]==[('M',x),('S',)]+w
     assert prefix(n-1,size+1)[0]==[('A',0,1,x+1)]+w
     cases+=1;maxbits=max(maxbits,n.bit_length())
 out={'status':'ABSTRACT_ADJACENT_PAIR_CORROBORATION_PASS','word_lengths':[1,2,3],'alphabet':alphabet,'positive_terminal_residuals':[1,2,3],'parameter_x':[0,1,2,7],'cases':cases,'largest_candidate_bit_length':maxbits,'scope':'Finite corroboration only. Uniform proof is in COFINAL_ADJACENT_PAIR_PROOF.md; no physical source binding asserted.'}
 assert json.loads(json.dumps(out))==json.loads((Path(__file__).resolve().parents[1]/'evidence/ADJACENT_PAIR_CHECK.json').read_text())
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();args.out.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out))
if __name__=='__main__':main()
