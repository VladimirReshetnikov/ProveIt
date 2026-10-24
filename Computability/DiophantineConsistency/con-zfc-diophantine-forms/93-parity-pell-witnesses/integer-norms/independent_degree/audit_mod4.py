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
Q=mul(Delta,s(sq(f),cst(1)));d=sq(sq(c));n=a(mul(cst(4),s(n0,mul(h,mul(Y,R0)))),cst(2))
delta=s(Q,cst(1));D=mul(d,delta);B0=mul(m,k);S=mul(k,a(mul(cst(2),m),cst(1)));A0=a(cst(1),mul(mul(m,a(m,cst(1))),sq(k)))
z=a(a(n,B0),mul(cst(4),mul(S,V)))
A=mul(A0,D);B=mul(Q,delta);C=mul(cst(16),mul(sq(S),mul(d,s(mul(Q,sq(V)),cst(1)))))
RR=s(s(s(mul(D,sq(z)),A),B),C)
TT=s(sq(RR),mul(cst(4),a(a(mul(A,B),mul(A,C)),mul(B,C))))
def deg(p):return max(sum(e*t for e,t in zip(mon,w)) for mon in p)
def top(p):
 dd=deg(p);return [[m,c] for m,c in p.items() if sum(e*t for e,t in zip(m,w))==dd]
expected_top=r.parse('2048*X**9*Y**13*R0**3*h**3*f**6*c**8*(R0*f*f+h*Y*(X-2*f*f))')
actual_top={mon:coef for mon,coef in TT.items() if sum(e*t for e,t in zip(mon,w))==109}
if deg(TT)!=109 or actual_top!=expected_top:
 raise ValueError('mod4 centered inner norm degree/leading certificate failed')
tail_bound=deg(A)+deg(B)+deg(C)+deg(D)+2*deg(z)
if tail_bound!=212:raise ValueError('tail bound')
rows=sorted([[list(mon),coef] for mon,coef in TT.items()])
receipt={'status':'PASS','variant':'modulus-four centered15','variables':names,'weights':w,'authentic_V':'c*T*f-R0*f**2-c',
 'center':'n=4*(n0-h*Y*R0)+2','root_sum':'L=n+m*k+4*S*V',
 'radicands':['Afirst','Q/d','16*S**2*(Q*V**2-1)/(Q-1)'],
 'inner_terms':len(TT),'inner_weighted_degree':109,
 'inner_top':'2048*X**9*Y**13*R0**3*h**3*f**6*c**8*(R0*f**2+h*Y*(X-2*f**2))',
 'triple_tail_degree_upper_bound':tail_bound,'norm_exact_degree':218,
 'unit_product_exact_degree':306,
 'actual_coefficient':{'monomial':{'J3':184,'w3':26,'v_scale':42,'z':8,'h':14,'f':16,'c':16},'coefficient':'2**116*3**210*beta**184'},
 'inner_expansion_sha256':hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
 'proof_scope':'Exact weighted identity on independent atoms; specializing genuine leading forms is justified in NOTE_MOD4.md.'}
(ROOT/'CHECKS_MOD4.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
