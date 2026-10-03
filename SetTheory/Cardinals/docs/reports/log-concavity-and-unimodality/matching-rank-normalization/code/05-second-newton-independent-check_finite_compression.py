"""Exact finite-graph checks of the signed-vector class-compression identity."""
from reconstruct import hall,minor_count,need,OUT
from itertools import combinations
from collections import Counter
import random,json
rng=random.Random(671923)
checked=0
for trial in range(48):
 core=tuple(rng.randrange(8) for _ in range(3));J,C1,C2=core
 L=[1,2,4]+[rng.randrange(1,8) for _ in range(rng.randrange(5))]
 R=[1,2,4]+[rng.randrange(1,8) for _ in range(rng.randrange(6))]
 rows=[sum(((core[b]>>i)&1)<<b for b in range(3))+sum(((mask>>i)&1)<<(3+j) for j,mask in enumerate(R)) for i in range(3)]+L
 def count(cols):
  return sum(hall(tuple(sum(((rows[i]>>c)&1)<<j for j,c in enumerate(cols)) for i in subset)) for subset in combinations(range(len(rows)),len(cols)))
 E=count((0,));need(E>0,'forced root empty')
 inds=list(range(1,3+len(R)));a=[count((0,i)) for i in inds]
 z=[rng.randrange(-3,4) for _ in inds]
 actual=sum(4*x*x*v*v for x,v in zip(a,z))
 for i,j in combinations(range(len(inds)),2):actual+=2*z[i]*z[j]*(4*a[i]*a[j]-5*E*count((0,inds[i],inds[j])))
 n=sum(bool(mask&1) for mask in L)
 rr={S:n*S.bit_count()+minor_count((J,S)) for S in range(1,8)}
 xx=a[:2];X={S:sum(z[j+2] for j,mask in enumerate(R) if mask==S) for S in range(1,8)}
 vals=z[:2]+[X[S] for S in range(1,8)];single=xx+[rr[S] for S in range(1,8)]
 classform=sum(4*x*x*v*v for x,v in zip(single,vals))
 # Subtract the diagonal pseudo-triple in each exterior class.
 classform-=5*E*sum((n*minor_count((S,S))+minor_count((J,S,S)))*X[S]**2 for S in range(1,8))
 q=count((0,1,2));classform+=2*z[0]*z[1]*(4*xx[0]*xx[1]-5*E*q)
 for b in range(2):
  for S in range(1,8):
   # Add one virtual R column and count its triple supports directly.
   rs=[row|((S>>i&1)<<(3+len(R))) if i<3 else row for i,row in enumerate(rows)]
   cc=(0,b+1,3+len(R))
   triple=sum(hall(tuple(sum(((rs[i]>>c)&1)<<j for j,c in enumerate(cc)) for i in subset)) for subset in combinations(range(len(rows)),3))
   classform+=2*z[b]*X[S]*(4*xx[b]*rr[S]-5*E*triple)
 for S,T in combinations(range(1,8),2):classform+=2*X[S]*X[T]*(4*rr[S]*rr[T]-5*E*(n*minor_count((S,T))+minor_count((J,S,T))))
 correction=5*E*sum((n*minor_count((mask,mask))+minor_count((J,mask,mask)))*z[j+2]**2 for j,mask in enumerate(R))
 need(actual==classform+correction,('compression mismatch',core,L,R,z))
 checked+=1
out={'all_pass':True,'finite_graph_signed_vector_checks':checked,'seed':671923}
(OUT/'finite_compression.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
