"""Exact weighted outer-product certificate; no floating decisions."""
from exact_intervals import *
R=iv(F(2,5));N=1024;Z=512;worst=-1;where=None;start=time.time()
for cell in range(N):
 l=F(N+cell,N);h=F(N+cell+1,N)
 c1=crng(l/2,h/2);c2=crng(l/4,h/4)
 s1=srng(l/2,h/2,'down');s2=srng(l/4,h/4,'up')
 c1=I(c1.lo,min(0,c1.hi));c2=I(max(0,c2.lo),c2.hi)
 s1=I(max(0,s1.lo),min(S,s1.hi));s2=I(max(0,s2.lo),min(S,s2.hi))
 A=c1*c2;B=srng(3*l/4,3*h/4,'down');C=s1*s2
 assert A.hi<=0 and C.lo>=0
 aa=4*A*C*R.square();bb=2*B*R*(A+C*R.square());cc=(A-C*R.square()).square()+B.square()*R.square()
 tail=iv(1)
 for j in range(3,15):
  lo=l/F(2**j);hi=h/F(2**j)
  tail=tail*(crng(lo,hi)+R*srng(lo,hi,'up'))
 # For j>=15, sum pi*x/2^j=pi*x/2^14; product(1+R theta_j)<=1/(1-R sum theta_j).
 eta=R*PI*iv(h/F(2**14));assert eta.hi<S
 tail=tail/(1-eta);tsq=tail.square()
 # Bound h(dist(x,Z)) from below on this entire x-cell.
 tl,th=(l-1,h-1) if h<=F(3,2) else (2-h,2-l)
 denominator=iv(1)
 for j in range(1,15):
  denominator=denominator*(crng(tl/F(2**j),th/F(2**j))+R*srng(tl/F(2**j),th/F(2**j),'up'))
 hlo=max(S,denominator.lo) # h>=1, and every omitted positive small-angle factor is at least1.
 for k in range(Z):
  z=I(iv(F(-Z+2*k,Z)).lo,iv(F(-Z+2*k+2,Z)).hi)
  bnd=(cc+bb*z+aa*z.square())*tsq
  normalized=-((-bnd.hi*S*S)//(hlo*hlo))
  if normalized>worst:worst=normalized;where=[cell,k]
  assert normalized*10000 <2401*S,(cell,k,F(normalized,S))
result=dict(statement='sup |H_a(x)|/H_(2/5)(dist(x,Z)) < 49/100 for |a|<=2/5 and 1<=|x|<=2',x_cells=N,cos_phase_cells=Z,fixed_point_scale=str(S),machin_pi_lower=str(plo),machin_pi_upper=str(phi),squared_bound_upper=str(F(worst,S)),squared_threshold='2401/10000',worst_cell=where,all_cells_strict=True)
Path(__file__).with_name('weighted_outer_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
