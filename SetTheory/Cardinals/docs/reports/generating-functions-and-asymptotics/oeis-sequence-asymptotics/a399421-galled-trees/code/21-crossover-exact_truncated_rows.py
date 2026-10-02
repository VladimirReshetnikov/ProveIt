"""Exact gall-degree-truncated enumeration; discarded higher degrees cannot affect lower ones."""
import json, math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
N=640
K=12
G=[[0] for _ in range(N+1)]; S=[[0] for _ in range(N+1)]
def addto(a,b,shift=0):
 if len(a)<min(K+1,len(b)+shift):a.extend([0]*(min(K+1,len(b)+shift)-len(a)))
 for j,x in enumerate(b):
  if j+shift<=K:a[j+shift]+=x

def conv(a,b):
 c=[0]*min(K+1,len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if i+j<=K:c[i+j]+=x*y
 return c

def square_co(n,seq):
 c=[0]
 for i in range(1,n): addto(c,conv(seq[i],seq[n-i]))
 return c
for n in range(1,N+1):
 a=square_co(n,G)
 if n%2==0:
  for j,x in enumerate(G[n//2]):
   if 2*j>K:break
   if len(a)<=2*j:a.extend([0]*(2*j+1-len(a)))
   a[2*j]+=x
 b=square_co(n-1,S)
 if n%2==1:
  for j,x in enumerate(S[(n-1)//2]):
   if 2*j>K:break
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
out={'rows':G,'max_leaf_degree':N,'max_gall_degree':K,'arithmetic':'exact integers; all polynomial products truncated in gall degree'}
reference=json.loads((ROOT/'data/reference-truncated-rows.json').read_text())
assert out==reference, 'Truncated reference mismatch'
full=json.loads((ROOT/'results/exact-rows.json').read_text())['rows']
assert all(row==full[n][:K+1] for n,row in enumerate(G[:161]))
(ROOT/'results/exact-truncated-rows.json').write_text(json.dumps(out)+'\n')
(ROOT/'results/truncated-checks.json').write_text(json.dumps({'max_leaf_degree':N,'max_gall_degree':K,'reference_match':True,'full_triangle_overlap_n':160,'arithmetic':'exact integer'},indent=2)+'\n')
print('Finished exact truncated rows:', N, K)
