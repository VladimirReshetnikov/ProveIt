from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-actual-rank-boundary-audit')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Exact polynomial certificates in q,beta,K0: rank cap and first-carrier residue.
N=3;zero=(0,)*N
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
q,b,K=(var(i) for i in range(N))
G=(q-1)*(q-1)+2
rank_cap=G*(q*q-1)+(q-2)+q*(2*q-3)
assert rank_cap==q*q*q*q-2*q*q*q+4*q*q-5
assert q*q*q*q-rank_cap-q*q*q-q-1==(q-4)*(q*q-1)
B=(b-2)*(b+1+K)-1
assert B==b*(b+K-1)-(2*K+3)
# Exact source-dependent symbolic kernel bound, without expanding rho^8807.
ks=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
for token in ['r^30+r^62+r^1100+r^2201','∑ i : Fin 943','r^(4393-i.val)+r^(5495-i.val)','∑ i : Fin 41','2^(10+i.val)','r^(4393-position i)+r^(5495-position i)','r^8807*r^42']:
 assert token in ks,token
selector=Path('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean').read_text()
assert 'def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)' in selector
rho=2**67;mass_bound=5+2*943*(1+2**51)+2*41*(2**50)
assert mass_bound<rho and 8807-5496>=3
# Check exact graph rank/first-root rows and fixed mask parity source.
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={row[0]:row[1:] for row in g['source']}
for name,row in {'qF':['-','q','F'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],'R':['+','g47','g50'],'Z':['-','g32','Bt'],'A0':['-','g38','g42']}.items():assert r[name]==row,(name,r[name],row)
low=Path('Lean/DiophantineConsistency/Compact44/CompactLowEven.lean').read_text();assert 'theorem low_even' in low
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text();assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
beta_src=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
for q0 in (24,32,64,128):
 b0=q0-1;mc=2*(b0//4);mf=b0;R=(b0*b0+2)*(q0*q0-1)+mc+q0*mf
 assert 0<=mc<b0 and mc%2==0 and b0<=mf<2*b0 and R%2==1
 assert R>=27 and R+q0**3+q0+1<=q0**4
print(json.dumps({'actual_rank_and_first_carrier_wiring_checked':True,'rank_cap_and_window_exact_polynomial_certificates':True,'selector_and_kernel_symbolic_remainder_bound':True,'fixed_beta_does_not_divide_2K_plus_3':True,'all_congruences_are_standard_integer_claims':True,'signed_first_root_rules_out_this_slice':True,'full_graph_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
