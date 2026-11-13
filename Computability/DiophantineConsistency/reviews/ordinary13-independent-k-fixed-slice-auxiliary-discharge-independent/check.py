from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixed-slice-auxiliary-discharge-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-independent-k-fixed-slice-auxiliary-discharge','ordinary13-independent-k-fixed-slice-conditional','ordinary13-independent-k-actual-rank-boundary-audit'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Build the odd x/I and odd ordinate polynomials independently in Z[A].
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def neg(a):return [-x for x in a]
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def scale(a,n):return [x*n for x in a]
def clean(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
# Substitute t=1-A² directly into P_l and compare Q_l.
t=[1,0,-1];K=add(scale(t,4),[-2]);L=[-2,0,4]
p0=[1];p1=add(scale(t,4),[-3]);q0=[1];q1=[-1,0,4];c0=1;c1=-3
for l in range(16):
 assert clean(p0[:])==clean(scale(q0,(-1)**l))
 assert c0==(-1)**l*(2*l+1)
 c0,c1=c1,-2*c1-c0
 p0,p1=p1,clean(add(mul(K,p1),neg(p0)))
 q0,q1=q1,clean(add(mul(L,q1),neg(q0)))
# Independently find matrix period in (Z/c²Z), then reconstruct both Pell
# pairs and exact CRT quotient for small bases. No periods are assumed.
def pell(A,n):
 x,y=1,0;Delta=A*A-1
 for _ in range(n):x,y=A*x+Delta*y,x+A*y
 return x,y
controls=[]
for a in range(4):
 A=a+2;Delta=A*A-1;R=3;g,c=pell(A,R);m=c*c;x,y=1,0
 for h in range(1,200000):
  x,y=(A*x+Delta*y)%m,(x+A*y)%m
  if (x,y)==(1,0):break
 else:raise AssertionError('period search limit')
 assert h<=c**8
 f,v=pell(A,h);assert v>0 and v%(c*c)==0
 i=Delta*(v//(c*c));I=i*c*c
 assert i>0 and I>1 and I==Delta*v and I*I==Delta*(f*f-1)
 x,y=pell(I,R);assert x%I==0;V=x//I
 assert f*f%c==1%c and V%(f*f)==(-c)%(f*f) and V%c==(-R)%c
 assert math.gcd(f*f,c)==1
 T,rem=divmod(V+f*f*R+c,f*f*c)
 assert rem==0 and T>=1 and V==f*f*(T*c-R)-c
 assert y*y-I*I*(y*y-V*V)==1
 controls.append({'a':a,'R':R,'h_found':h,'c':c})
# Fixed slice: q ≡ 0 (mod 4), MC ≡ 2 (mod 4), G=q*t−1.
for q in (4,8,12,16):
 for t0 in range(1,9):
  for MF in range(8):
   for MC in (2,6,10):
    R=(q*t0-1)*(q*q-1)+MC+q*MF
    assert R%4==3 and ((R-1)//2)%2==1
# Both main-root signs modulo 3: a≡H≡0, q≡g≡d≡2.
for a in range(0,30,3):
 H=3+4*a
 for c in range(1,8):
  for gamma0 in range(-3,4):
   d=2+a*c+H*gamma0
   assert d%3==2 and (-2)%3!=d%3
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
mask=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in mask and '}) \\ {1}' in mask
recipe=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in recipe
assert 'Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j' in recipe
assert 0 in (set(range(943))-{1}) and 0!=1063 and (2**67-2)%4==2
print(json.dumps({'three_author_receipts_reproduced':True,'chebyshev_polynomial_checks':16,'independent_positive_period_crt_controls':controls,'fixed_rank_mod4_checked':True,'negative_main_sign_mod3_excluded':True,'fixed_main_condition_decided':False,'graph_zero_or_global_zero_equivalence_established':False,'lean_executed':False},sort_keys=True,indent=2))
