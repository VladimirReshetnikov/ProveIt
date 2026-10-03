import json
from pathlib import Path
import sympy as s
D=Path(__file__).parent;R=json.loads((D/'cover3_seventeen_templates.json').read_text())
for idx in [1,3,10]:
 r=R[idx];g=list(map(s.sympify,r['gamma_monomial']));C=s.Symbol('n4');A=s.expand(g[1]-C);B=s.expand(g[2]-A*C)
 assert s.expand(g[3]-B*C)==0
 delta=s.expand(A*A-4*B)
 if idx==1:
  n1,n2,n3=s.symbols('n1 n2 n3');assert s.expand(delta-((n1-n2)**2+2*n3**2+2*n3))==0
 else:assert all(v>=0 for e,v in s.Poly(delta).terms())
 assert s.expand(s.sympify(r['gap_monomial'])-(B-A*C/2)**2-s.Rational(3,4)*C*C*delta)==0
 print('product certificate verified',idx)
a,b,c=s.symbols('n3 n4 n7');p=s.sympify(R[9]['gap_monomial']);base=s.sympify(R[10]['gap_monomial']);uni=s.expand((p-base).subs({a:0,b:0}));rest=s.expand(p-base-uni)
assert all(v>=0 for e,v in s.Poly(rest,a,b,c).terms())
assert s.expand(uni-sum(v*s.prod(c-j for j in range(k))/s.factorial(k)for k,v in enumerate([0,4,41,57,18])))==0
print('extension certificate verified 9')
p2=s.sympify(R[2]['gap_monomial']);p3=s.sympify(R[3]['gap_monomial']);assert s.expand(p2.subs({'n1':0,'n5':0,'n7':0})-p3.subs('n1',0))==0
print('missing-face reduction verified 2')
for idx in [11,13,15,16]:
 r=R[idx];xs=s.symbols(' '.join('n'+str(t)for t in r['types']),seq=True)
 assert all(v>=0 for q,v in r['gap_binomial'])
 p=sum(v*s.prod(s.prod(x-j for j in range(k))/s.factorial(k)for x,k in zip(xs,q))for q,v in r['gap_binomial'])
 assert s.expand(p-s.sympify(r['gap_monomial']))==0
 print('binomial certificate verified',idx)
r=R[0];assert not r['core_arcs'] and r['signs']==[-1,-1,-1] and r['types']==list(range(1,8))
print('class0 is source-core/target-exterior bipartite rank<=3; uses the previously proved bipartite support ULC theorem')
