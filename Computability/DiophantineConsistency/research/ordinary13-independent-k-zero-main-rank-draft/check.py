from pathlib import Path
from hashlib import sha256
import json, random, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-zero-main-rank-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():
 assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json')
g=json.loads(p.read_text()); assert len(g['source'])==84 and g['witnesses'][10]=='n_k'
def ev(w,ports):
 d=dict(zip(g['witnesses'],w)); d.update(zip(g['fixed_numerals'],ports))
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a; y=d[b] if isinstance(b,str) else b
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
rng=random.Random(6173)
for _ in range(800):
 beta=rng.randrange(3,18); J=rng.randrange(1,10); q=1+beta*J
 F=rng.randrange(1,q+1); alpha=rng.randrange(1,q+1); eta=rng.randrange(20)
 w=[J,F-1,alpha-1,rng.randrange(8),rng.randrange(8),rng.randrange(8),rng.randrange(1,8),rng.randrange(8),rng.randrange(8),eta,0,rng.randrange(8),rng.randrange(8)]
 ports=[beta,rng.randrange(8),rng.randrange(beta),rng.randrange(2*beta)]
 d=ev(w,ports); X=d['X']; Y=d['Y']; a=X*Y+Y; H=3+4*a; U=Y*q*q
 R=((q-1)*(q-F)+alpha)*(q*q-1)+J*(ports[2]+q*ports[3])
 assert d['R']==R and d['Dstar']==U*(X+a*eta)+H*(U*w[12]+R+1)
 assert d['A1']==d['Dstar']**2-U**2*(1+(H+a*a)*eta**2)
 assert U==q**5*(w[7]+1) and d['Z']==(q-1)*w[8]-d['Bt']
# Exact polynomial identity behind the weak-gap bound, in Z[q].
# q⁴ − (q³+2q²−2q) = q(q−1)(q²−2).
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
assert mul(mul([0,1],[-1,1]),[-2,0,1])==[0,2,-2,-1,1]
assert [0,2,-2,-1,1]==[0,2,-2,-1,1] # coefficient order q^0..q^4
# Integer controls for the two first-norm branches and weak-gap rank bound.
neg=eq=0
for beta in range(3,9):
 for J in range(1,5):
  q=1+beta*J; b=q-1
  for F in range(1,q+2):
   for alpha in range(1,q+2):
    C=q-F-alpha
    for w in (1,2):
     X=q*w
     for K in (0,1,7):
      Bt=C*(X+K)-F
      if C<0:
       assert -Bt>=X+F>b
       for r in (0,1,2): assert (b*r-Bt)**2>b*b
       neg+=1
      elif C==0:
       for r in (0,1,2):
        if (b*r-Bt)**2==b*b:
         assert r==0 and F==b and alpha==1;eq+=1
  for MC in (0,beta-1):
   for MF in (0,2*beta-1):
    mask=J*(MC+q*MF)
    assert mask<(q-1)*(1+2*q)
    R=q*(q*q-1)+mask
    assert R+1<q**4
# Factor-three finite checks, including q divisible by 3; unrestricted t samples.
count=0
for q in range(2,15):
 for s in (1,2):
  for X in range(5):
   Y=q**3*s; H=3+4*Y*(X+1)
   for t in list(range(1,101))+[q**4,q**5,3*q**4]:
    if (H*t)%(q**5)==0: assert t%(q**4)==0
    count+=1
src=(D/'IndependentKZeroMainRank.lean.src').read_text()
for x in ['(hR : R+1<q^4)','(hq : 0<q)','(hs : 0<s)','ModelRelationCombining.sq_dvd_sq','natural_dvd_of_signed','cancel_factor_three']:
 assert x in src
print(json.dumps({'graph_controls':800,'first_gap_negative_controls':neg,'first_gap_equality_witness_controls':eq,'factor_three_controls':count,'independent_k_graph_full_zero_proved':False,'source_elaborated':False,'lean_executed':False},indent=2,sort_keys=True))
