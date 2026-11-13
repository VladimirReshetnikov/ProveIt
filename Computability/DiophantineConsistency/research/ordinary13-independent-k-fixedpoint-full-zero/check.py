from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-fixedpoint-full-zero')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Reproduce the independently reviewable predecessor algebra/CRT receipts.
for name in ['ordinary13-independent-k-actual-rank-boundary-audit','ordinary13-independent-k-fixed-slice-auxiliary-discharge']:
 p=Path('research')/name
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
N=67*8807;assert N==590069;mod=N
root=Path('Lean/DiophantineConsistency/Compact44')
# Parse the actual ordered 943-row data and compact selector slots.
text=(root/'Compact943Data.lean').read_text();body=text.split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,x)) for x in re.findall(r'^\s*\(\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)\s*\)',body,re.M)]
slots_src=(root/'CompactSymbolicKernel.lean').read_text();slots=[int(x) for x in re.search(r'def slots : List ℕ := \[([^]]+)\]',slots_src).group(1).split(',')]
assert len(rows)==943 and len(slots)==41 and all(0<=x<4393 for x in slots)
assert 'def rho : ℕ := 2^67' in slots_src
beta_src=(root/'CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
ports_src=(root/'CompactSymbolicPorts.lean').read_text()
assert 'def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)' in ports_src
assert 'def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits' in ports_src
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports_src
c44=(root/'C44Short15Facts.lean').read_text()
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in c44
selector_src=(root/'CompactCoefficientMass.lean').read_text()
for token in ['t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34','1 + 2^10 * (2^41 - value t)']:
 assert token in selector_src,token
kernel=(root/'CompactSymbolicKernelOpaque.lean').read_text()
for token in ['r^30+r^62+r^1100+r^2201','∑ i : Fin 943','r^(4393-i.val)+r^(5495-i.val)','∑ i : Fin 41','2^(10+i.val)','r^(4393-position i)+r^(5495-position i)','r^8807*r^42']:
 assert token in kernel,token
rho=pow(2,67,mod);q=pow(2,N,mod);beta=(q-1)%mod
kp=(pow(rho,42,mod)+sum(pow(rho,e,mod) for e in (30,62,1100,2201)))%mod
for i,(a,b,c,d) in enumerate(rows):
 value=a+2**8*b+2**17*c+2**25*d+127*2**34
 assert 0<value<2**41
 selector=1+2**10*max(0,2**41-value)
 kp=(kp+selector*(pow(rho,4393-i,mod)+pow(rho,5495-i,mod)))%mod
for i,pos in enumerate(slots):
 kp=(kp+pow(2,10+i,mod)*(pow(rho,4393-pos,mod)+pow(rho,5495-pos,mod)))%mod
# Horner evaluation of exact least-significant-first low/high digit recipes.
mask=(root/'CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in mask
assert '{1063,1064,1095,2195,3296}) \\ {1}' in mask
listmask=(root/'CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in listmask
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
MC=0
for j in range(8806,-1,-1):
 digit=(rho-(4 if j==1063 else 2 if j in support else 1))%mod
 MC=(MC*rho+digit)%mod
high_src=(root/'CompactHighPopulation.lean').read_text()
for token in ['def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1','[4] ++ List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]']:
 assert token in high_src,token
mu=2**51-2;padding=2**65-1;last=2**19-1
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[mu]+[0]*1101+[mu]+[0]*3296+[padding]*13+[last,0]
assert len(high)==8807
H=0
for digit in reversed(high):H=(H*rho+digit)%mod
MF=(beta+H)%mod
A=((q*q-1-q*kp)*(q*q-1)+MC+q*MF)%mod
B=(q*(q*q-1))%mod
solutions=[];power=1
for e in range(N):
 if (A-B*power-e)%N==0:solutions.append(e)
 power=power*2%N
assert solutions==[439547];e=solutions[0];power_e=pow(2,e,N)
assert (rho,q,beta,kp,MC,H,MF,A,B,power_e)==(299894,273473,273472,551654,428453,73733,347205,365222,460162,55048)
F=(kp+power_e)%N;alpha=(beta-F)%N
rank=((alpha+(q-F)*beta)*(q*q-1)+MC+q*MF)%N
assert rank==e and (A-B*power_e)%N==e
assert 67*5496<e and e+1<N-1 and N>=24 and N%2==1
# Algebraic identities for carrier, first root, actual rank and main shift.
# Scalars are formal integer polynomials in b,Kp,P,z,h,k,tau,ell,q,S.
M=10;zero=(0,)*M
class Poly:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return Poly(r)
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(x+y for x,y in zip(k,j));r[key]=r.get(key,0)+v*w
  return Poly(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,Poly) else Poly({zero:x})
def v(i):
 e0=[0]*M;e0[i]=1;return Poly({tuple(e0):1})
b,Kp,P,z,h,k,tau,ell,qq,S=(v(i) for i in range(M))
w=P+b*z; X=(b+1)*w; K0=b*h+Kp; F=Kp+P
assert X+K0-F==b*(w+h+z)
B0=b*(w+h+z);hh=w+h+z;rw=tau-ell-k+(k*b+1)*hh
assert b*(ell+k+rw-k*B0)-B0==b*tau
U=qq*qq*qq*qq*qq; MM=qq*qq*qq*qq*qq*qq*qq*w
assert 4*MM*S==U*(4*qq*qq*w*S)
# Generalized-X finite controls; proof of the uniform growth bound is in README.
def pell(A0,j):
 xx,yy=1,0;DD=A0*A0-1
 for _ in range(j):xx,yy=A0*xx+DD*yy,xx+A0*yy
 return xx,yy
for q0 in (24,30):
 for w0 in (1,2,5):
  n0=14;X0=q0*w0;Y0=q0**3;M0=X0*Y0*Y0
  tau0,y0=pell(2*M0+1,n0);k0=2*y0;g0,c0=pell(Y0*(X0+1)+2,2*n0-1)
  assert tau0*tau0==1+M0*(M0+1)*k0*k0
  assert c0>(Y0+1)*k0 and c0-Y0*k0>k0
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rr={x[0]:x[1:] for x in g['source']}
for name,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'Bt':['-','g27','F'],'R':['+','g47','g50'],'Z':['-','g32','Bt'],'Dstar':['+','g58','g59'],'g72':['-','g71','Q'],'Fa':['-','y2','g82'],'out':['-','P0123',1]}.items():assert rr[name]==row,(name,rr[name],row)
print(json.dumps({'N':N,'row_count':len(rows),'slot_count':len(slots),'residues_mod_N':{'rho':299894,'q':273473,'beta':273472,'Kprime':551654,'MC':428453,'high':73733,'MF':347205,'A':365222,'B':460162,'two_pow_e':55048},'fixed_point_e':e,'all_fixed_points_mod_N':solutions,'F_alpha_and_w_symbolic_bounds_checked':True,'carrier_first_and_main_scaling_polynomial_identities':True,'general_X_growth_small_controls':6,'fixed_compact_numbers_or_pell_coordinates_materialized':False,'lean_executed':False,'claim':'Standard integer symbolic full child zero, subject to the written recurrence and CRT proof; not a model or parent-zero equivalence.'},sort_keys=True,indent=2))
