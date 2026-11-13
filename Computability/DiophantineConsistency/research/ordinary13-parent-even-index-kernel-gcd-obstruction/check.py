#!/usr/bin/env python3
"""Bounded exact controls for the kernel-gcd same-data obstruction."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-index-coprime-discriminant-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
g=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());rows={x[0]:x[1:] for x in g['source']}
for k,v in {'I':['*','c2','i'],'Q':['*','Delta','rho'], 'g72':['-','g71','Q'],
 'Fs':['+',1,'g72'],'V':['-','g76','c'],'y2':['*','n_y','n_y'],
 'Fa':['-','y2','g82'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[k]==v,(k,rows[k])
def kernel(D):
 n=D;d=t=1;p=2
 while p*p<=n:
  e=0
  while n%p==0:n//=p;e+=1
  if e:d*=p**(e%2);t*=p**(e//2)
  p+=1
 if n>1:d*=n
 return d,t
def ycoord(A,m):
 D=A*A-1;x,y=1,0
 for _ in range(m):x,y=A*x+D*y,x+A*y
 return y
special=[];controls=0
for A in range(2,50):
 D=A*A-1;d,t=kernel(D);assert D==d*t*t
 for m in range(2,16,2):
  c=ycoord(A,m);g=math.gcd(c*c,d*t)
  if math.gcd(m,t)==1:assert c%g==0
  if c%g==0 and math.gcd(m,t)>1 and (A,m) in ((3,4),(8,6)):
   special.append({'A':A,'Delta':D,'d':d,'t':t,'m':m,'c':c,
                   'gcd_c_squared_dt':g,'gcd_m_t':math.gcd(m,t),
                   'gcd_m_Delta':math.gcd(m,D)})
  controls+=1
assert len(special)==2
# Direct c² divisibility => c divisibility of u under the stated gcd criterion.
count=0
for c in range(1,50):
 for b in range(1,50):
  g=math.gcd(c*c,b)
  if c%g:continue
  for u in range(1,100):
   if (b*u)%(c*c)==0:assert u%c==0;count+=1
# Bounded anti-diagonal controls also include odd and even h.
def pell(A,n,mod):
 D=(A*A-1)%mod;x,y=1,0
 for _ in range(n):x,y=(A*x+D*y)%mod,(x+A*y)%mod
 return x,y
primes=[p for p in range(3,70,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
prime_cases=0
for A in range(2,15):
 for h in range(1,10):
  for p in primes:
   x,y=pell(A,h,p)
   if x==0:
    assert y!=0
    for odd in range(1,60,2):assert pell(A,odd,p)[1]!=0
    prime_cases+=1
# Crucial strict control: c² need not divide the A-Pell ordinate itself.
A=2;m=6;h=1560;D=A*A-1;c=ycoord(A,m);assert c==780
_,v=pell(A,h,c*c)
assert v==202800 and v!=0 and (D*v)%(c*c)==0
print(json.dumps({'prior_coprime_discriminant_receipt_reproduced':True,
 'bounded_Pell_kernel_criterion_controls':controls,'kernel_cancellation_controls':count,
 'anti_diagonal_prime_controls_including_odd_h':prime_cases,
 'strict_A_pell_ordinate_control':{'A':2,'m':6,'h':1560,'c':c,'v_mod_c_squared':v},
 'strict_extra_criterion_examples':special,
 'conditional_same_data_parent_completion_excluded':True,
 'fixed_compact_two_norm_zero_proved':False,'existential_inequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
