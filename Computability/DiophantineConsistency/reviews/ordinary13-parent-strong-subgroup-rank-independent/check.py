from pathlib import Path
from hashlib import sha256
import json,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-parent-strong-subgroup-rank-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expr(g):
 e={v:('var',v) for v in g['witnesses']+g['fixed_numerals']}
 for n,op,a,b in g['source']:e[n]=(op,e[a] if isinstance(a,str) else ('lit',a),e[b] if isinstance(b,str) else ('lit',b))
 return e
p,q=expr(parent),expr(child)
for x in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[x]==q[x]
r={v[0]:v[1:] for v in parent['source']}
for k,v in {'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],'rho':['-','f2',1],
 'Q':['*','Delta','rho'],'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],
 'Fs':['+',1,'g72'],'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],
 'V':['-','g76','c'],'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'F0':['+',1,'A0'],'F1':['+',1,'A1'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'out':['-','P0123',1]}.items():assert r[k]==v
# Discover independent integer-coordinate fundamental norm-one units.
ds=[2,3,5,6,7,10,11,13,15];units={}
for d in ds:
 for x in range(2,2000):
  if (x*x-1)%d:continue
  u=math.isqrt((x*x-1)//d)
  if u>0 and x*x-d*u*u==1:units[d]=(x,u);break
 assert d in units

def seq(d,a,b,n):
 x,y=1,0;out=[(x,y)]
 for _ in range(n):x,y=a*x+d*b*y,b*x+a*y;out.append((x,y))
 return out
cases={'even_rm':0,'odd_rm':0};hits=0
for d,(a,b) in units.items():
 S=seq(d,a,b,90)
 for r0 in range(1,5):
  A,t=S[r0];assert A*A-d*t*t==1 and A>t
  for m in range(2,12):
   N=r0*m;k=N//2;U=S[N][1];Uk=S[k][1]
   assert U>m*t*Uk
   if m%2:
    v=m//2;cases['even_rm' if N%2==0 else 'odd_rm']+=1
    if N%2==0:
     assert k>=r0*v+1 and 2*S[k][0]>=4*S[r0*v][0]>=4*v*A>m*t
    else:
     assert k>=r0*v and U>2*a*S[k][0]*Uk>=4*v*A*Uk>m*t*Uk
   assert U%t==0;c=U//t;g0=math.gcd(c,d*t)
   assert g0==math.gcd(m,d*t) and c//g0>Uk
   for h in range(1,2*N+1):
    if (d*t*S[h][1])%c==0:
     assert h%N==0
     f=S[h][0];assert (f*f-1)%c==0
     hits+=1
assert all(cases.values()) and hits>0
# Fixed strong f,I: test both correlated signs, numerator divisibility,
# positivity and factor equation, including the known odd-index toy.
def pell(A,n):
 delta=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
A=2;m=3;f,v=pell(A,15);c=pell(A,m)[1];I=3*v
assert c==15 and I%(c*c)==0 and f*f-1==3*v*v and (f*f-1)%c==0
checks=success=0
for ell in (1,3,5,7):
 x,y=pell(I,ell);assert x%I==0
 j=(ell-1)//2;yell=pell(A,ell)[1]
 for eps in (-1,1):
  sigma=eps*((-1)**j);V=eps*(x//I)
  for R in range(-20,31):
   numerator=V+c+f*f*R
   conditions=((yell+sigma*c)%(f*f)==0 and (ell+sigma*R)%c==0)
   assert (numerator%(f*f*c)==0)==conditions
   if conditions and numerator>0:
    T=numerator//(f*f*c)
    assert T>=1 and V==f*f*(T*c-R)-c
    assert y*y-I*I*(y*y-V*V)==1
    success+=1
   checks+=1
assert success>0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'parent_auxiliary_rows_checked':True,'odd_growth_branch_controls':cases,
 'subgroup_hits_checked':hits,'both_sign_numerator_controls':checks,
 'positive_auxiliary_controls':success,'ordinary_pell_classification_assumed':True,
 'actual_graph_zero_constructed':False,'lean_executed':False},indent=2,sort_keys=True))
