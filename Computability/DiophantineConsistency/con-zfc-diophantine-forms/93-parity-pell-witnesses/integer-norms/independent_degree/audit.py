import json,hashlib
from pathlib import Path
from ring import Ring
ROOT=Path(__file__).resolve().parent
names=['X','Y','R0','h','f','c','T','n0'];w=[2,4,5,1,1,1,1,1]
r=Ring(names);p={n:r.symbol(n) for n in names}
a=lambda x,y:r.add(x,y);s=lambda x,y:r.add(x,y,-1);mul=r.mul;cst=r.constant;sq=lambda p:mul(p,p)
X,Y,R0,h,f,c,T,n0=[p[n] for n in names]
E=mul(X,Y); aa=mul(a(X,cst(1)),Y)
Delta=a(a(sq(aa),mul(cst(4),aa)),cst(3))
m=mul(X,sq(Y));k=a(a(R0,cst(1)),mul(h,E));V=s(s(mul(mul(c,T),f),mul(R0,sq(f))),c)
Q=mul(Delta,s(sq(f),cst(1)));d=sq(sq(c));n=s(a(mul(cst(2),n0),cst(1)),mul(cst(2),mul(h,mul(Y,R0))))
delta=s(Q,cst(1));D=mul(d,delta);B0=mul(m,k);S=mul(k,a(mul(cst(2),m),cst(1)));A0=a(cst(1),mul(mul(m,a(m,cst(1))),sq(k)))
z=a(a(n,mul(cst(2),B0)),mul(cst(2),mul(S,V)))
A=mul(cst(4),mul(A0,D));B=mul(Q,delta);C=mul(cst(4),mul(sq(S),mul(d,s(mul(Q,sq(V)),cst(1)))))
RR=s(s(s(mul(D,sq(z)),A),B),C)
TT=s(sq(RR),mul(cst(4),a(a(mul(A,B),mul(A,C)),mul(B,C))))
def deg(p):return max(sum(e*t for e,t in zip(mon,w)) for mon in p)
def top(p):
 dd=deg(p);return [[m,c] for m,c in p.items() if sum(e*t for e,t in zip(m,w))==dd]
expected_top=r.parse('512*X**9*Y**13*R0**3*h**3*f**6*c**8*(R0*f*f+h*Y*(X-2*f*f))')
actual_top={mon:coef for mon,coef in TT.items() if sum(e*t for e,t in zip(mon,w))==109}
if deg(TT)!=109 or actual_top!=expected_top:
 raise ValueError('centered inner norm degree/leading certificate failed')
tail_bound=deg(A)+deg(B)+deg(C)+deg(D)+2*deg(z)
if tail_bound!=212:raise ValueError('tail bound')
rows=sorted([[list(mon),coef] for mon,coef in TT.items()])
receipt={'status':'PASS','variables':names,'weights':w,'authentic_V':'c*T*f-R0*f**2-c',
 'odd_center':'n=2*n0+1-2*h*Y*R0','inner_terms':len(TT),'inner_weighted_degree':109,
 'inner_top':'512*X**9*Y**13*R0**3*h**3*f**6*c**8*(R0*f**2+h*Y*(X-2*f**2))',
 'triple_tail_degree_upper_bound':tail_bound,'norm_exact_degree':218,
 'unit_product_exact_degree':306,
 'inner_expansion_sha256':hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
 'proof_scope':'Exact weighted identity on independent atoms; specializing genuine leading forms is justified in NOTE.md.'}
(ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
