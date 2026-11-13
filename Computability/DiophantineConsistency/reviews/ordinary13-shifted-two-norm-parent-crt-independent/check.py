from pathlib import Path
from hashlib import sha256
import json,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-shifted-two-norm-parent-crt-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
root=Path('research/ordinary13-shifted-two-norm-parent-crt-sufficient-condition')
p=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
t=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expr(g):
 v={s:('var',s) for s in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:
  a=v[a] if isinstance(a,str) else ('lit',a);b=v[b] if isinstance(b,str) else ('lit',b);v[name]=(op,a,b)
 return v
pe,te=expr(p),expr(t)
for name in ['A0','A1','R','a','c','H','Delta','Dstar']:assert pe[name]==te[name]
rows={r[0]:r[1:] for r in p['source']}
expected={'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],
 'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],
 'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'F0':['+',1,'A0'],
 'F1':['+',1,'A1'],'Fs':['+',1,'g72'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}
for n,r in expected.items():assert rows[n]==r,(n,rows[n])
# Independent direct polynomial recurrence in A, P_j(1-A²)=(-1)^j y_(2j+1)(A).
def norm(p):
 while p and p[-1]==0:p.pop()
 return p
def add(p,q):return norm([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return [-x for x in p]
def mul(p,q):
 if not p or not q:return []
 r=[0]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):r[i+j]+=x*y
 return norm(r)
# p0=1, p1=1-4 A², pnext=(2-4 A²)*pcur-pprev.
p0=[1];p1=[1,0,-4]; y0=[1];y1=[-1,0,4];coef=[-2,0,4]
assert p0==y0 and p1==neg(y1)
at0prev=1;at0cur=-3
for j in range(2,21):
 at0prev,at0cur=at0cur,-2*at0cur-at0prev
 p0,p1=p1,add(mul([2,0,-4],p1),neg(p0))
 y0,y1=y1,add(mul(coef,y1),neg(y0))
 assert p1==(y1 if j%2==0 else neg(y1))
 assert at0cur==(-1)**j*(2*j+1)
# Matrix powering independent of the supplied checker.
def mm(a,b,m):return tuple(sum(a[i*2+k]*b[k*2+j] for k in range(2))%m for i in range(2) for j in range(2))
def mp(a,n,m):
 r=(1,0,0,1)
 while n:
  if n&1:r=mm(r,a,m)
  a=mm(a,a,m);n//=2
 return r
for A in range(2,10):
 delta=A*A-1;Q=(A,delta,1,A);f,v=1,0
 for h in range(1,10):
  f,v=A*f+delta*v,f+A*v
  assert f*f-delta*v*v==1
  assert mp(Q,4*h*f,f*f)==(1,0,0,1)
# An independent fact-level CRT sample; not a full graph zero.
A=2;delta=3;c=15;m=3;h=90;f,v=1,0
for _ in range(h):f,v=A*f+delta*v,f+A*v
assert v%(c*c)==0 and math.gcd(f,c)==1
I=delta*v;assert I*I==delta*(f*f-1)
P=4*h*f;R=18;L=3
assert m%4==3 and (R-m)%math.gcd(4*h,c)==0
assert (L-m)%P==0 and (L-R)%c==0
V=4*I*I-3;y=4*I*I-1;num=V+c+f*f*R
assert num%(f*f*c)==0 and num//(f*f*c)==2
assert y*y-I*I*(y*y-V*V)==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'shared_expression_trees':8,
 'parent_auxiliary_rows_checked':len(expected),'chebyshev_polynomial_instances':21,
 'matrix_period_instances':72,'fact_level_toy_checked':True,
 'source_only':True,'unconditional_lift_proved':False,'lean_executed':False},indent=2,sort_keys=True))
