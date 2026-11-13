from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-parent-even-main-strong-pell-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expr(g):
 e={v:('var',v) for v in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:
  e[name]=(op,e[a] if isinstance(a,str) else ('num',a),e[b] if isinstance(b,str) else ('num',b))
 return e
p,q=expr(parent),expr(child)
for x in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[x]==q[x]
rows={r[0]:r[1:] for r in parent['source']}
for x,r in {'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],
 'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],
 'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'F0':['+',1,'A0'],
 'F1':['+',1,'A1'],'Fs':['+',1,'g72'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[x]==r

def pell(A,n,mod=None):
 x,y=1,0;d=A*A-1
 for _ in range(n):
  x,y=A*x+d*y,x+A*y
  if mod is not None:x%=mod;y%=mod
 return x,y
# Quotient divisibility criterion and the source's convention for both signs.
for I in range(3,18):
 for j in range(40):
  x,y=pell(I,j)
  assert (x%I==0)==(j%2==1)
  if j%2:assert (-x)%I==0
  assert x*x-(I*I-1)*y*y==1
primes=[n for n in range(3,32,2) if all(n%d for d in range(2,math.isqrt(n)+1))]
cases=sign_checks=0
for A in range(2,10):
 delta=A*A-1
 for h in range(2,14,2):
  f,v=pell(A,h)
  assert f==2*pell(A,h//2)[0]**2-1 and f%2==1
  for prime in primes:
   if f%prime:continue
   assert delta*v*v%prime==prime-1 and v%prime!=0
   # Traverse the complete finite-state cycle, remembering index parity.
   states=[];seen=set();x,y,parity=1,0,0
   while (x,y,parity) not in seen:
    seen.add((x,y,parity));states.append((x,y,parity))
    x,y,parity=(A*x+delta*y)%prime,(x+A*y)%prime,1-parity
   assert (x,y,parity)==(1,0,0)
   assert all(y!=0 for x,y,parity in states if parity)
   I=delta*v; t=I*I%prime; prev,cur=1,(4*t-3)%prime
   # P_j(t) = x_(2j+1)(I)/I; check recurrence and both signs.
   for j in range(len(states)):
    ell=2*j+1;yell=states[ell%len(states)][1]
    assert prev%prime==((-1 if j%2 else 1)*yell)%prime
    for m in (2,4,6):
     c=pell(A,m,prime)[1]
     assert yell!=c and yell!=(-c)%prime
     assert prev%prime not in {(-c)%prime,c}
     sign_checks+=2
    prev,cur=cur,((4*t-2)*cur-prev)%prime
   cases+=1
assert cases>0 and sign_checks>0
# Direct Lucas identity including negative indices.
def y(A,j):return (-1 if j<0 else 1)*pell(A,abs(j))[1]
for A in range(2,8):
 for m in (2,4,6):
  for ell in (1,3,5,7):assert y(A,ell)**2-y(A,m)**2==y(A,ell-m)*y(A,ell+m)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'parent_auxiliary_and_output_rows_checked':True,
 'bounded_full_modular_cycles':cases,'bounded_auxiliary_sign_checks':sign_checks,
 'even_and_odd_multiplier_tested':True,'standard_pell_classification_assumed':True,
 'other_strong_witness_families_excluded':False,'lean_executed':False},indent=2,sort_keys=True))
