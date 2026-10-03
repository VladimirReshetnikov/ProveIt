"""Exact proof-method barrier, using only integer polynomial arithmetic."""
from itertools import combinations
import json,pathlib
# Six times binom(n,h), h=0..3, increasing powers of n.
CH=[(6,),(0,6),(0,-3,3),(0,2,-3,1)]
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 while len(c)>1 and c[-1]==0:c.pop()
 return tuple(c)
def scale(a,w):return tuple(w*x for x in a)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def hall(rows):
 for size in range(1,len(rows)+1):
  for ids in combinations(range(len(rows)),size):
   mask=0
   for i in ids:mask|=rows[i]
   if mask.bit_count()<size:return False
 return True
# Right variables 0,1 are B2,B3; variables 2,3 are private leaves at A1,A2.
def support(S,core):
 k=S.bit_count();out=(0,)
 for I in range(8):
  h=k-I.bit_count()
  if not 0<=h<=3:continue
  rows=[]
  for i in range(3):
   if I>>i&1:
    neighbors=(S&3) if core else 0
    if i<2:neighbors|=S&(1<<(i+2))
    rows.append(neighbors)
  rows.extend([S&3]*h)
  if hall(rows):out=add(out,CH[h])
 return out

def gap(core):
 T=[support(S,core) for S in range(16)];out=(0,)
 for S in range(16):
  if S.bit_count()==2:out=add(out,scale(mul(T[S],T[15^S]),8))
  if S.bit_count()==1:out=add(out,scale(mul(T[S],T[15^S]),-15))
 return out
raw=add(gap(True),scale(gap(False),-1))
assert raw==(2016,-144),raw
out={'status':'passed','36_times_increment_coefficient_in_powers_of_n':raw,'coefficient':'56 - 4*n','first_negative_integer_n':15,'value_at_15':-4}
path=pathlib.Path(__file__).resolve().parent.parent/'data'/'barrier_verification.json'
path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
