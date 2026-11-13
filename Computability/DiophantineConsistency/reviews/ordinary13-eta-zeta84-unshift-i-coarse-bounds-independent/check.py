from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta84-unshift-i-coarse-bounds-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
child=json.loads(Path('research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text())
rows=[['n_i' if x=='i' else x for x in row] for row in parent['source'] if row!=['i','+','n_i',1]]
assert len(rows)==84 and rows==child['source']
# Independently prove exponent equality for all L by comparing polynomials in L.
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def clean(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
L=[0,1];n=[0,1,2];m=add(n,L)
left=mul(add(add(m,L),[1]),add(m,[-1]))
right=add(add(L,[1]),mul(add(add(m,[0,2]),[2]),add(n,[-1])))
assert clean(left)==clean(right)
L=2172;n=L*(2*L+1);m=n+L;q=128;beta=127;K=87;MC=54;MF=139;F=119;alpha=8
R=(alpha+(q-F)*beta)*(q*q-1)+MC+q*MF
assert (n,m,R)==(9437340,9439512,18874679) and R==2*n-1
assert beta>=46 and K>0 and MC<beta and beta<=MF<2*beta
assert (beta%8,beta%3,MC%8,(MF-beta)%8)==(7,1,6,4)
assert q-F-alpha==1 and m%7==5 and pow(2,m,beta)==32 and (32+K-F)%beta==0
# 4(m−1)Y < X follows solely from m<2^24 and L+26<m.
assert n>=14 and m>n and m<2**24 and L+26<m and L>=21
# Independently reconstruct another exact small power-matched full child zero.
def pell(A,j):
 x,y=1,0;d=A*A-1
 for _ in range(j):x,y=A*x+d*y,x+A*y
 return x,y
q=4;L=12;n=L*(2*L+1);m=n+L;beta=3;K=3;MC=2;MF=108;F=1;alpha=2
X=2**m;Y=2**L;M=X*Y*Y;U=Y*q*q;a=Y*(X+1);H=3+4*a
R=(alpha+(q-F)*beta)*(q*q-1)+MC+q*MF
assert R==2*n-1
(tau,yfirst)=pell(2*M+1,n);k=2*yfirst;(g,c)=pell(a+2,m);eta=c-Y*k
assert 0<eta<k and c>X
Bt=X+K-F;assert Bt%beta==0;h=Bt//beta
r=tau-M*k-k+(k*beta+1)*h
assert (k-R-1)%U==0 and (g-X-a*c)%H==0
gamma=(k-R-1)//U+(g-X-a*c)//H
w=[1,F-1,alpha-1,1,0,0,X//q,Y//q**3-1,r,eta,k-eta,1,gamma];p=[beta,K,MC,MF]
assert min(w)>=0
def ev(G):
 d=dict(zip(G['witnesses'],w));d.update(zip(G['fixed_numerals'],p))
 for name,op,x,y in G['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
x=ev(child);y=ev(parent)
assert (x['A0'],x['A1'],x['g72'],x['Fa'],x['out'])==(0,0,0,1,0)
assert y['out']==c**4>0
print(json.dumps({'author_receipt_reproduced':True,'child_one_row_delta_exact':True,'power_matching_exponent_polynomial_identity':True,'coarse_bounds_rank_and_divisibility_checked':True,'large_growth_bound_exponents_checked_without_expansion':True,'independent_small_full_graph_control':{'q':4,'L':12,'n':n,'m':m,'c_bit_length':c.bit_length()},'actual_fixed_compact_tuple_covered':False,'lean_executed':False},sort_keys=True,indent=2))
