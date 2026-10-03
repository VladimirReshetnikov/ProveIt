import sympy as S,itertools,json
from pathlib import Path
p=S.symbols('p0:4');q=S.symbols('q0:4');r=p[0];s=q[0]
e2=lambda x:sum(a*b for a,b in itertools.combinations(x,2))
sq=lambda x:sum(a*a for a in x)
BP=e2(p);BQ=e2(q);LP=sum(p);LQ=sum(q);H=BP*BQ-LP*LQ+1+r*s
ray=lambda x,y:S.diff(H,x)*S.diff(H,y)-H*S.diff(H,x,y)
checks={}
# same side, one distinguished
A=sum(p[2:]);U=sq(p[2:]);B=sum(q[1:]);V=sq(q[1:])
checks['same_distinguished']=(p[0],p[1],((BQ*A-B)**2+BQ**2*U+V)/2)
# same side, neither distinguished
A=p[0]+p[3];U=p[3]**2
checks['same_ordinary']=(p[1],p[2],((BQ*A-LQ)**2+(BQ*r-s)**2+BQ**2*U+V)/2)
# opposite sides, both distinguished
A=sum(p[1:]);U=sq(p[1:]);B=sum(q[1:]);V=sq(q[1:])
checks['cross_both_distinguished']=(p[0],q[0],(A*A*V+B*B*U)/2)
# opposite sides, one distinguished
B=q[0]+sum(q[2:]);V=sq(q[2:])
checks['cross_one_distinguished']=(p[0],q[1],((A*(B+s)-2)**2+A*A*V+U*((B-s)**2+V))/4)
# opposite sides, neither distinguished
A=p[0]+sum(p[2:]);U=sq(p[2:])
checks['cross_neither_distinguished']=(p[1],q[1],((A*B-r*s-2)**2+(A*s-r*B)**2+U*(B*B+s*s)+V*(A*A+r*r)+U*V)/4)
for name,(x,y,ss) in checks.items():
 diff=S.Poly(S.expand(ray(x,y)-ss),*p,*q)
 assert diff.is_zero,(name,diff)
 print(name,'passed')
out={'checks':list(checks),'parallel_classes_per_side':4,'all_symbolic_identities':True,'status':'passed; formulas have arbitrary-class proofs in the note'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
