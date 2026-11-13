from pathlib import Path
from hashlib import sha256
import sys,json,subprocess,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-actual-rank-boundary-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-independent-k-actual-rank-boundary-audit','ordinary13-independent-k-shared-index-norm-audit'):
 p=Path('research')/name
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rows={r[0]:r[1:] for r in g['source']}
for name,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'qF':['-','q','F'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],'g30':['+','ell','n_k'],'g31':['+','g30','n_r'],'folded_kBt':['*','n_k','Bt'],'folded_g31':['-','g31','folded_kBt'],'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],'R':['+','g47','g50']}.items():assert rows[name]==row,(name,rows[name])
# Independent rank-cap identity in Z[q], coefficient arrays low degree first.
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
q=[0,1];q2=mul(q,q)
gcoef=add(mul([-1,1],[-1,1]),[2]);cap=add(mul(gcoef,[-1,0,1]),add([-2,1],mul(q,[-3,2])))
assert cap==[-5,0,4,-2,1]
# Check compact least digit source, top-level port selection, and coefficient recipe.
support=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in support and '{1063,1064,1095,2195,3296}) \\ {1}' in support
mask=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in mask
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert '![β,K,L,β+H]' in ports and '8807 1063 CompactConcreteMask.support' in ports
kernel=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
for token in ('r^30+r^62+r^1100+r^2201','∑ i : Fin 943','r^(4393-i.val)+r^(5495-i.val)','∑ i : Fin 41','2^(10+i.val)','r^(4393-position i)+r^(5495-position i)','r^8807*r^42'):
 assert token in kernel
sel=Path('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean').read_text()
assert '1 + 2^10 * (2^41 - value t)' in sel
rho=2**67;T=5+2*943*(1+2**51)+2*41*2**50
assert T<rho and 8807-5496>=3
# Check the growth comparison in cases q<2n+2: the reused proof is uniform
# under its own q>=24,n>=9 hypotheses, not the old family parameter range.
for q0 in (24,25,32,50):
 for n in (14,31,50,100):
  assert q0**(n-4)>4*6**(n-1)
  assert q0**(8*n-8)>4*6**(n-1)*q0**(7*n-4)
assert 24<2*100+2
# Integer arithmetic controls for the first-root square divisibility implication.
for b in range(1,50):
 for B in range(-25,26):
  for u in range(-3,4):
   Z=b*u-B
   if Z*Z%(b*b)==0:assert B%b==0
print(json.dumps({'author_and_growth_receipts_reproduced':True,'graph_rank_and_first_root_wiring_checked':True,'compact_rank_cap_coefficient_identity':True,'least_digit_and_kernel_recipe_sources_checked':True,'kernel_coefficient_bound_below_radix':True,'growth_checked_beyond_old_q_versus_n_condition':True,'slice_first_root_divisibility_controls':True,'global_zero_map_or_model_claim':False,'lean_executed':False},sort_keys=True,indent=2))
