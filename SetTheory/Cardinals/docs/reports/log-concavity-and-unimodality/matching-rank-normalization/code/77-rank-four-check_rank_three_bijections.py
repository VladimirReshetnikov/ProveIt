import itertools,json
from math import comb
T=range(1,8)
def feasible(types,centers):
 return any(all(t>>c&1 for t,c in zip(types,p)) for p in itertools.permutations(centers))
pair=[];triple=[]
for types in itertools.combinations_with_replacement(T,2):
 fac=sum(feasible(types,centers) for centers in itertools.combinations(range(3),2))
 if fac:pair.append((types,fac))
for types in itertools.combinations_with_replacement(T,3):
 if feasible(types,range(3)):triple.append(types)
def multip(n,types):
 val=1
 for t in set(types):val*=comb(n[t-1],types.count(t))
 return val
def compositions(total,parts):
 if parts==1:yield (total,);return
 for first in range(total+1):
  for rest in compositions(total-first,parts-1):yield (first,)+rest
out=[];checks=0
for total in range(3,13):
 negative=[]
 for n in compositions(total,7):
  a=sum(t.bit_count()*n[t-1] for t in T)
  b=sum(f*multip(n,t) for t,f in pair)
  c=sum(multip(n,t) for t in triple)
  if not c:continue
  checks+=1;D=a*a*b*b-4*a*a*a*c-4*b*b*b-27*c*c+18*a*b*c
  if D<0:negative.append((n,[1,a,b,c],D))
 if negative:
  out=negative;break
assert total==12 and checks==48987
assert out==[((0,0,4,0,4,4,0),[1,24,162,208],-2592)]
print(json.dumps({'status':'PASS','method':'Bijection feasibility tables with recursive weak compositions','first_right_population':total,'negative':out,'rank3_vectors_checked':checks},indent=2))
