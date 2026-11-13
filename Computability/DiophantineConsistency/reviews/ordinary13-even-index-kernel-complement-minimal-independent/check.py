from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-even-index-kernel-complement-minimal-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
G=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text());rows={r[0]:r[1:] for r in G['source']}
for n,r in {'q':['+',1,'qm'],'s':['+','n_s',1],'q2':['*','q','q'],'q3':['*','q','q2'],
 'Y':['*','q3','s'],'X':['*','q','n_w'],'E':['*','X','Y'],'a':['+','E','Y'],
 'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],
 'g19':['*','a','c'],'b0':['+','X','g19'],'U':['*','Y','q2'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}.items():assert rows[n]==r,(n,rows[n])
# The first integer-coordinate norm-one unit for d=2 is exactly (3,2).
for f in (2,):
 for u in range(1,f+1):assert f*f-2*u*u!=1
assert 3*3-2*2*2==1
A=3;delta=8;c=6;m=2;assert 17**2-delta*c*c==1
assert math.gcd(c*c,4)==4 and c%4!=0
for c0 in range(1,200):assert c0%math.gcd(c0*c0,3)==0
x,y=1,0;seq=[]
for h in range(1,7):x,y=3*x+8*y,x+3*y;seq.append((x,y))
assert [y%9 for x,y in seq]==[1,6,8,6,1,0]
f,y=seq[-1];I=8*y
assert (f,y,I,I//36)==(19601,6930,55440,1540) and I%36==0
assert I*I==8*(f*f-1)
for f0 in range(2,f):
 z=math.isqrt(8*(f0*f0-1))
 assert z*z!=8*(f0*f0-1) or z%36!=0
assert f%17==0 and I%17==3
# Full 4-cycle of the odd quotient polynomial at I²=9 mod 17.
t=I*I%17;p0=1;p1=(4*t-3)%17;quot=[]
for _ in range(4):quot.append(p0);p0,p1=p1,((4*t-2)*p1-p0)%17
assert (p0,p1)==(1,(4*t-3)%17) and set(quot)=={1,16}
assert c%17 not in quot and (-c)%17 not in quot
# Complete finite-field parity cycles for A=3, for all small odd prime divisors
# of Pell abscissas; scalar/anti-diagonal contradiction covers arbitrary h.
primes=[p for p in range(3,100,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
cases=0
for p in primes:
 states=[];seen=set();x,y,par=1,0,0
 while (x,y,par) not in seen:
  seen.add((x,y,par));states.append((x,y,par));x,y,par=(3*x+8*y)%p,(x+3*y)%p,1-par
 assert (x,y,par)==(1,0,0)
 if any(x==0 for x,y,par in states):
  assert all(y!=0 for x,y,par in states if par)
  cases+=1
assert cases>0
# For the actual A=3 graph, Y*(X+1)=1 forces Y=1 and X=0.
for Y in range(1,8):
 for X in range(8):
  if Y*(X+1)==1:assert (Y,X)==(1,0)
# With q³*s=1 and q,s positive, q=s=1; then U=1,H=7,a=1.
for q in range(1,8):
 for s in range(1,8):
  if q**3*s==1:assert (q,s)==(1,1)
# If d=c mod7 the main norm d²−8c²=1 is impossible for every c.
for c in range(7):
 for d in range(7):
  if (d-c)%7==0:assert (d*d-8*c*c)%7!=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'lexicographic_minimum_and_strong_minimum_checked':True,'finite_mod17_quotient_cycle_checked':True,
 'full_modular_antidiagonal_cycles':cases,'actual_graph_A3_obstruction_checked':True,
 'integer_pell_classification_assumed':True,'graph_zero_constructed':False,'lean_executed':False},indent=2,sort_keys=True))
