"""Portable replay adapter; the original arithmetic is unchanged.
All inputs and output destinations are explicit command-line options.
"""
import argparse, json, math
from pathlib import Path
parser=argparse.ArgumentParser(description="Generate exact bivariate coefficient rows.")
parser.add_argument('--max-n', type=int, default=160)
parser.add_argument('--output', type=Path, required=True)
args=parser.parse_args()
N=args.max_n
if N < 1: parser.error('--max-n must be positive')
G=[[0] for _ in range(N+1)]; S=[[0] for _ in range(N+1)]
def addto(a,b,shift=0):
 if len(a)<len(b)+shift:a.extend([0]*(len(b)+shift-len(a)))
 for j,x in enumerate(b):a[j+shift]+=x

def conv(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):c[i+j]+=x*y
 return c

def square_co(n,seq):
 c=[0]
 for i in range(1,n): addto(c,conv(seq[i],seq[n-i]))
 return c
for n in range(1,N+1):
 a=square_co(n,G)
 if n%2==0:
  for j,x in enumerate(G[n//2]):
   if len(a)<=2*j:a.extend([0]*(2*j+1-len(a)))
   a[2*j]+=x
 b=square_co(n-1,S)
 if n%2==1:
  for j,x in enumerate(S[(n-1)//2]):
   if len(b)<=2*j:b.extend([0]*(2*j+1-len(b)))
   b[2*j]+=x
 addto(a,b,1)
 assert all(x%2==0 for x in a)
 G[n]=[x//2 for x in a]
 if n==1:G[n][0]+=1
 while len(G[n])>1 and not G[n][-1]:G[n].pop()
 c=G[n].copy()
 for i in range(1,n):addto(c,conv(G[i],S[n-i]))
 S[n]=c
 print(n, len(str(sum(G[n])))) if n%40==0 else None
out={'rows':G,'totals':[sum(a) for a in G], 'statistics':[]}
for n in [20,40,80,160]:
 if n>N:continue
 a=G[n];t=sum(a);m=sum(k*x for k,x in enumerate(a))/t;v=sum(k*k*x for k,x in enumerate(a))/t-m*m
 out['statistics'].append({'n':n,'mean':m,'variance':v,'mean_per_n':m/n,'variance_per_n':v/n})
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(out)+'\n')
print(out['totals'][:28]);print(out['statistics'])
