from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-actual-rank-boundary-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-actual-rank-boundary-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'qm':('*','n_J','beta'),'q':('+',1,'qm'),'X':('*','q','n_w'),
'qF':('-','q','F'),'C':('-','qF','alpha'),'g26':('+','X','K0'),'g27':('*','C','g26'),
'Bt':('-','g27','F'),'G':('+','alpha','g44'),'g47':('*','G','g46'),
'R':('+','g47','g50'),'Z':('-','g32','Bt'),'A0':('-','g38','g42')}.items():assert r[n]==row
assert g['witnesses'][0:3]==['n_J','n_F','n_alpha']
ks=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
for x in ('r^30+r^62+r^1100+r^2201','∑ i : Fin 943','∑ i : Fin 41','r^8807*r^42','r^(4393-i.val)+r^(5495-i.val)','r^(4393-position i)+r^(5495-position i)'):assert x in ks
assert 'def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)' in Path('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean').read_text()
assert 'theorem low_even' in Path('Lean/DiophantineConsistency/Compact44/CompactLowEven.lean').read_text()
rho=2**67;T=5+2*943*(1+2**51)+2*41*2**50
assert T<rho and 8807-5496>=3
for q in (24,32,64,128,256):
 b=q-1
 for mc in range(0,b,2):
  for mf in (b,2*b-1):
   rank=(b*b+2)*(q*q-1)+mc+q*mf
   assert rank%2==1 and rank<=q**4-2*q**3+4*q*q-5
   assert q**4-(rank+q**3+q+1)>=(q-4)*(q*q-1)>=0
   for K in (1,17,1000):
    first=(q-3)*(q+K)-1
    assert first==b*(b+K-1)-(2*K+3)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'actual_graph_rank_and_carrier_rows_checked':True,
 'kernel_term_and_mass_bound_checked':True,'finite_rank_and_remainder_controls':True,
 'scope':'One fixed-coordinate slice; no full zero-map or model proof.',
 'lean_executed':False},sort_keys=True,indent=2))
