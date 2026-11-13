from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-parent-even-index-kernel-gcd-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expr(g):
 e={x:('var',x) for x in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:e[name]=(op,e[a] if isinstance(a,str) else ('lit',a),e[b] if isinstance(b,str) else ('lit',b))
 return e
p,q=expr(parent),expr(child)
for name in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[name]==q[name]
rows={r[0]:r[1:] for r in parent['source']}
for name,body in {'i':['+','n_i',1],'f2':['*','n_f','n_f'],'rho':['-','f2',1],
 'Q':['*','Delta','rho'],'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],
 'Fs':['+',1,'g72'],'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],
 'V':['-','g76','c'],'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'F0':['+',1,'A0'],'F1':['+',1,'A1'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'out':['-','P0123',1]}.items():assert rows[name]==body
# g|c is exactly the condition for cancellation c²|b*u => c|u for all integer u.
for c in range(1,120):
 for b in range(1,120):
  g=math.gcd(c*c,b);u=c*c//g
  assert b*u%(c*c)==0
  assert (c%g==0)==(u%c==0)
  if c%g==0:
   for k in range(4):assert (u*k)%c==0
# Independently factor Delta and verify the claimed sufficient special cases.
def kernel(n):
 d=t=1;p=2
 while p*p<=n:
  e=0
  while n%p==0:n//=p;e+=1
  d*=p**(e%2);t*=p**(e//2);p+=1
 if n>1:d*=n
 return d,t
def pell(A,n,mod=None):
 d=A*A-1;x,y=1,0
 for _ in range(n):
  x,y=A*x+d*y,x+A*y
  if mod:x%=mod;y%=mod
 return x,y
special=0
for A in range(2,70):
 delta=A*A-1;d,t=kernel(delta);assert d*t*t==delta
 for m in range(2,18,2):
  c=pell(A,m)[1];g=math.gcd(c*c,d*t)
  assert math.gcd(c,t)==math.gcd(m,t)
  if math.gcd(m,t)==1 or t==1:assert c%g==0
  if c%g==0 and math.gcd(m,t)>1:special+=1
assert special>0
A=8;m=6;delta=63;d,t=kernel(delta);c=pell(A,m)[1]
assert (d,t,c,math.gcd(c*c,d*t),math.gcd(m,t))==(7,3,1032240,3,3)
A=2;m=6;delta=3;c=pell(A,m)[1];h=1560
f,y=pell(A,h,c*c)
assert c==780 and y==202800 and y!=0 and delta*y%(c*c)==0
assert math.gcd(m,delta)==3 and math.gcd(c*c,delta)==3
# Complete modular states and index parity, including p=2, validate both signs.
primes=[2,3,5,7,11,13,17,19,23,29,31];cases=0
for A in range(2,10):
 delta=A*A-1
 for prime in primes:
  states=[];seen=set();x,y,parity=1%prime,0,0
  while (x,y,parity) not in seen:
   seen.add((x,y,parity));states.append((x,y,parity))
   x,y,parity=(A*x+delta*y)%prime,(x+A*y)%prime,1-parity
  assert (x,y,parity)==(1%prime,0,0)
  for h in range(1,2*len(states)):
   xh,yh,ph=states[h%len(states)]
   if xh!=0:continue
   assert yh!=0 and (delta*yh*yh+1)%prime==0
   assert all(yj!=0 for xj,yj,pj in states if pj==1)
   cases+=1
assert cases>0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'parent_auxiliary_rows_checked':True,
 'cancellation_criterion_exact_in_unrestricted_integer_u':True,
 'weaker_special_cases_and_strict_illustrations_checked':True,
 'anti_diagonal_controls_including_prime_two':cases,
 'integer_pell_classification_assumed':True,'conditional_same_data_only':True,
 'lean_executed':False},indent=2,sort_keys=True))
