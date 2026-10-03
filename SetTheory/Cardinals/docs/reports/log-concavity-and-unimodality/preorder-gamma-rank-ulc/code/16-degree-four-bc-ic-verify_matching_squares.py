import sympy as S,itertools,json
from pathlib import Path
p=S.symbols('p0:4');q=S.symbols('q0:4');r0,r1=p[:2];s0,s1=q[:2]
e2=lambda x:sum(a*b for a,b in itertools.combinations(x,2))
sq=lambda x:sum(a*a for a in x)
P=e2(p);Q=e2(q);L=sum(p);M=sum(q);K=r0*s0+r1*s1;H=P*Q-L*M+1+K
ray=lambda x,y:S.diff(H,x)*S.diff(H,y)-H*S.diff(H,x,y)
checks={}
# Same-side distinguished pair.
A=sum(p[2:]);U=sq(p[2:]);B=sum(q[2:]);V=sq(q[2:])
checks['same_both_distinguished']=(p[0],p[1],((Q*A-B)**2+Q*Q*U+V)/2)
# Same-side one distinguished.
A=p[1]+p[3];U=p[3]**2
checks['same_one_distinguished']=(p[0],p[2],((Q*A-(M-s0))**2+(Q*r1-s1)**2+Q*Q*U+V)/2)
# Same-side ordinary pair.
A=r0+r1;U=S.Integer(0)
checks['same_ordinary']=(p[2],p[3],((Q*A-M)**2+(Q*r0-s0)**2+(Q*r1-s1)**2+Q*Q*U+V)/2)
# Opposite sides, partnered distinguished pair.
A=sum(p[1:]);U=sq(p[2:]);B=sum(q[1:]);V=sq(q[2:])
checks['cross_partnered']=(p[0],q[0],((A*s1-B*r1)**2+A*A*V+B*B*U)/2)
# Opposite sides, unpartnered distinguished pair.
A=sum(p[1:]);u=p[1];U=sq(p[2:]);B=q[0]+sum(q[2:]);v=q[0];V=sq(q[2:])
checks['cross_unpartnered']=(p[0],q[1],((A*B+u*B+v*A-u*v-2)**2+U*(B-v)**2+V*(A-u)**2+U*V)/4)
# Opposite sides, distinguished vs ordinary.
A=sum(p[1:]);U=sq(p[2:]);B=q[0]+q[1]+q[3];V=q[3]**2;v=q[0];r=p[1];s=q[1]
checks['cross_one_distinguished']=(p[0],q[2],((A*(B+v)-r*s-2)**2+(A*s-r*(B-v))**2+V*(A*A+r*r)+U*((B-v)**2+s*s)+U*V)/4)
# Opposite sides, both ordinary.
A=p[0]+p[1]+p[3];U=p[3]**2;B=q[0]+q[1]+q[3];V=q[3]**2;R2=r0*r0+r1*r1;S2=s0*s0+s1*s1
checks['cross_ordinary']=(p[2],q[2],((A*B-K-2)**2+(A*s0-B*r0)**2+(A*s1-B*r1)**2+(r0*s1-r1*s0)**2+U*(B*B+S2)+V*(A*A+R2)+U*V)/4)
for name,(x,y,ss) in checks.items():
 diff=S.Poly(S.expand(ray(x,y)-ss),*p,*q);assert diff.is_zero,(name,diff);print(name,'passed')
out={'checks':list(checks),'parallel_classes_per_side':4,'all_symbolic_identities':True,'status':'passed; arbitrary-class proof uses aggregate identities'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
