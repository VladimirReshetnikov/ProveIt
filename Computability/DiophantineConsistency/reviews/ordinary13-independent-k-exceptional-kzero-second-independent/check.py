from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-exceptional-kzero-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for q in ('research/ordinary13-independent-k-exceptional-kzero-audit','reviews/ordinary13-independent-k-unit-norm-independent'):
 p=Path(q);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for n,row in {'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],
 'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],
 'g50':['*','n_J','g49'],'R':['+','g47','g50'],'q':['+',1,'qm'],
 'qm':['*','n_J','beta'],'qF':['-','q','F'],'C':['-','qF','alpha'],
 'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],
 'r0base':['-','n_k','R'],'r0':['-','r0base',1],'g54':['*','U','n_gamma'],
 'shift':['-','g54','r0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g65':['*','g62','g64'],
 'A1':['-','g61','g65']}.items():assert r[n]==row
# Direct integer identity under alpha=qF+t and beta*J=q-1.
for q in range(2,45):
 for qF in range(1,q):
  for t in range(5):
   for J in range(1,5):
    for MC,MF in ((0,0),(3,5)):
     R=(qF+t+qF*(q-1))*(q*q-1)+J*(MC+q*MF)
     u=J*MC+1-t
     assert R+1-u==q*(qF*(q*q-1)+t*q+J*MF)
# Check the limiting low mask digit directly from the pinned support recipe.
support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296};support.discard(1)
assert 8806 not in support and 8806!=1063
ls=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in ls
assert 'Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j' in ls
assert 'r^30+r^62+r^1100+r^2201' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
assert '![β,K,L,β+H]' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
# Independent bounded controls for the two strict interval endpoints.
cases=0
for beta in range(2,45):
 for M in range(beta):
  if 6*M<=5*beta:continue
  for J in range(1,6):
   q=1+J*beta
   for t in range((q-2)//7+1):
    u=J*M+1-t
    assert 2*q<3*u<3*q and (3*u)%q!=0
    cases+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'independent_factor_residue_receipt_reproduced':True,'graph_rank_rows_checked':True,
 'rank_identity_controls':True,'mask_highest_digit_controls':True,
 'interval_controls':cases,'lean_executed':False,'model_endpoint_proved':False},sort_keys=True,indent=2))
