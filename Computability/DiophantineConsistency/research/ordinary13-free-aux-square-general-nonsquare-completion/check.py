from pathlib import Path
from hashlib import sha256
import sys,json,math,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-general-nonsquare-completion')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-free-aux-square-main-norm-nonsquare-partial','ordinary13-free-aux-square-two-norm-positive-k-transfer'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
# Track exact graph dependencies of both norms: none of the four coordinates
# changed by the completion may appear in either residual.
d={name:{name} for name in g['witnesses']+g['fixed_numerals']}
for n,op,x,y in g['source']:
 d[n]=(d[x] if isinstance(x,str) else set()) | (d[y] if isinstance(y,str) else set())
changed={'n_f','n_i','n_T','n_y2'}
assert not(d['A0']&changed) and not(d['A1']&changed)
rows={x[0]:x[1:] for x in g['source']}
for n,row in {'Q':['*','Delta','rho'],'I':['*','c2','i'],'g72':['-','g71','Q'],'V':['-','g76','c'],'g81':['-','n_y2','V2'],'Fa':['-','n_y2','g82']}.items():assert rows[n]==row
# Verify the finite-field count by enumerating x,y for every nonzero D.
count=0
for p in (5,7,11,13,17,19,23,29,31):
 for D0 in range(1,p):
  pairs=sum(1 for x in range(p) for y in range(p) if (x*x-y*y-D0)%p==0)
  assert pairs==p-1
 for I in range(1,p):
  t=I*I%p;lead=t*(t-1)%p
  if not lead:continue
  def chi(x):
   x%=p
   return 0 if x==0 else 1 if pow(x,(p-1)//2,p)==1 else -1
  values=[chi(1+2*b*t+b*b*lead) for b in range(p)]
  assert sum(values)==-chi(lead) and -1 in values
  count+=1
# Complete graph control at a noncompact q=2; the fixed compact values
# and the corresponding period are never expanded.
def pell(A,n):
 d=A*A-1;x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+d*y*v,x*v+y*u
  u,v=u*u+d*v*v,2*u*v;n//=2
 return x,y
q=2;beta=1;Y=q**3;A=Y+2;delta=A*A-1;c=4*delta+3;R=402;alpha=133
x,y=1,0
for h in range(1,10000):
 x,y=(A*x+delta*y)%(c*c),(x+A*y)%(c*c)
 if (x,y)==(1,0) and h%2==0:break
else:raise AssertionError('toy period not found')
f,v=pell(A,h);I=delta*v
assert v%(c*c)==0 and f*f==1+delta*v*v and math.gcd(f,A)==1 and math.gcd(f*f,c)==1
FM=f*f;bf=((1+c)*pow(A*A,-1,FM))%FM
b0=bf+FM*(((R+1-bf)*pow(FM,-1,c))%c)
assert b0%(FM)==bf and b0%c==(R+1)%c
product=f*c*I*(I*I-1)
def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
p=next(p for p in range(5,200) if prime(p) and product%p)
for u in range(p):
 b=b0+FM*c*u;t=I*I;z=1+2*b*t+b*b*t*(t-1)
 if pow(z%p,(p-1)//2,p)==p-1:break
else:raise AssertionError('toy nonresidue search')
V=1+b*(I*I-1);num=V+FM*R+c;den=FM*c
assert num%den==0;T=num//den;i=I//(c*c)
assert T>=1 and i>0 and V==FM*(T*c-R)-c
k,eta=divmod(c,Y);zeta=k-eta;assert zeta>=0
vals=[1,0,alpha-1,f,i-1,T-1,0,0,0,eta,zeta,z,0];ports=[beta,0,0,0]
e=dict(zip(g['witnesses'],vals));e.update(zip(g['fixed_numerals'],ports))
for n,op,x,y in g['source']:
 x=e[x] if isinstance(x,str) else x;y=e[y] if isinstance(y,str) else y
 e[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
assert e['R']==R and e['c']==c and e['I']==I and e['V']==V and e['g72']==0 and e['Fa']==1
assert pow(z%p,(p-1)//2,p)==p-1
print(json.dumps({'two_predecessor_receipts_reproduced':True,'exact_first_main_dependencies_unchanged':True,'finite_field_character_sum_controls':count,'toy_q':q,'toy_even_period':h,'toy_prime':p,'toy_u':u,'toy_free_y2_bits':z.bit_length(),'toy_actual_strong_aux_checked':True,'compact_zero_existence_claimed':False,'lean_executed':False},sort_keys=True,indent=2))
