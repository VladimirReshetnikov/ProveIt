"""Independent small-dimensional digit/central-binomial audit, not an unbounded proof."""
from math import factorial
import random,json
from pathlib import Path
rng=random.Random(610895)
# Four-sum uniqueness for weights 1,5 with zero padding.
w=[1,5]; exps=[(a,b) for a in range(5) for b in range(5-a)]
assert len({a+5*b for a,b in exps})==len(exps)
polys=[{(1,0):1,(0,2):-1},{(2,0):1,(0,2):-1},{(0,0):-4,(1,0):1},{(1,1):1,(0,0):-6}]
b=8192;B=b**5;t=max(w);L=4*t;N0=B**(t+1);N1=4*B**(8*t+1);N=N0*N1
ell=sum(B**x for x in w); mask=N0-1-(b-1)*ell
T=mask+(B-2)*B**L*N0
assert 0<T<N
count=0;zeros=0
for pp in polys:
 cc={a:factorial(a[0])*factorial(a[1])*factorial(4-sum(a))*v for a,v in pp.items()}
 D=sum(v*B**(L-a[0]-5*a[1]) for a,v in cc.items())
 geom=(B**(8*t+1)-1)//(B-1)
 for x,y in [(x,y) for x in range(15) for y in range(15)]+[(rng.randrange(b),rng.randrange(b)) for _ in range(100)]:
  g=x*B+y*B**5
  P=sum(v*x**a[0]*y**a[1] for a,v in pp.items())
  J=2*(1+g)**4*D+B*geom
  assert J>0 and J<N1
  assert ((J & ((B-2)*B**L))==0)==(P==0)
  S=g+J*N0;assert 0<S<N
  R=(S+T+1)*N+T+1;X=(N-1)*R
  assert (X.bit_count()>=2*(N.bit_length()-1))==(P==0)
  count+=1;zeros+=P==0
out={'decoded_assignments':count,'zero_cases':zeros,'digit_and_binomial_agreement':True,'scope':'Four explicit toy polynomials, two-digit weights; not a solvability search for the ZFC instance.'}
Path(__file__).with_name('sparse_digit_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
