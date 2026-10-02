from state_search import f
from itertools import product
N=10
# dictionaries (x degree, T degree) -> integer
one={(0,0):1}
def add(*a):
 o={}
 for p in a:
  for k,v in p.items():o[k]=o.get(k,0)+v
 return {k:v for k,v in o.items() if v}
def mul(a,b):
 o={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():
   if i+k<=N:o[i+k,j+l]=o.get((i+k,j+l),0)+v*w
 return o
A=add({(1,0):1},{(i,1):1 for i in range(2,N+1)})
cT={(i,1):1 for i in range(1,N+1)}
IA=dict(one);v=dict(one)
for i in range(N):v=mul(v,A);IA=add(IA,v)
P={};Q={};D={}
for d in range(1,9):
 rhs=dict(one)
 for q in range(1,d):rhs=add(rhs,mul(Q[q],P[d-q]))
 D[d]=mul(IA,rhs);P[d]=add(one,mul(cT,D[d]));Q[d]=add(one,mul(A,D[d]))

def eval_op(op,n,h):
 return sum(v*f(n-i,h+r-1,0,(0,)) for (i,r),v in op.items() if i<=n)
checks=0
for k in range(0,4):
 for gaps in product(range(1,4),repeat=k):
  if sum(gaps)>8:continue
  op=one
  for d in gaps:op=mul(op,P[d])
  S=[0]
  for d in gaps:S.append(S[-1]+d)
  S=tuple(S)
  for h in range(1,4):
   for n in range(0,7):
    assert eval_op(op,n,h)==f(n,h+max(S)-1,0,S),(h,gaps,n,'E')
    checks+=1
   if gaps:
    opg=Q[gaps[0]]
    for d in gaps[1:]:opg=mul(opg,P[d])
    for n in range(0,7):
     assert eval_op(opg,n,h)==f(n,h+max(S)-1,gaps[0],S),(h,gaps,n,'G')
     checks+=1
print('PASS exact operator/state coefficient checks:',checks)
print('A202061 terms through 16:',[1]+[f(n-1,0,0,(0,)) for n in range(1,17)])
