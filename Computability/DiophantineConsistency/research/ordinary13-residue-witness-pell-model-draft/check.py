from pathlib import Path
from hashlib import sha256
import json,subprocess,sys,tempfile,shutil
p=Path('research/ordinary13-residue-witness-pell-model-draft')
files=[p/'generate.py',p/'ResidueExactIndexWitness.lean.src',p/'ResidueExactIndexGraphWitness.lean.src',p/'ResiduePellCoordinates.lean.src',p/'README.md',
Path('research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src'),
Path('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src'),
Path('research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src'),
Path('research/ordinary13-residue-qbalance-graph-draft/ResidueQBalanceGraph.lean.src'),
Path('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean'),
Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean'),
Path('Lean/DiophantineConsistency/ArithmeticPellCongruences.lean')]
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
# Execute the local generator in an isolated temporary tree; never mutate the
# original inputs, source drafts, or generated receipts.
with tempfile.TemporaryDirectory(prefix='residue-pell-') as d:
 root=Path(d)
 for f in [files[0],files[5],files[6]]:
  dest=root/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
 subprocess.run([sys.executable,'-I','-S','-B',str(files[0])],cwd=root,check=True)
 for f in files[1:3]:assert (root/f).read_bytes()==f.read_bytes(),str(f)
s=[f.read_text() for f in files]
for x in ['main_coordinate_of_norm','ArithmeticPellClassification.solution_index','ArithmeticPellCongruences.y_strictMono','graph_coordinates_and_balance','hfirst','hmainy','direct_main_orientation','⟨main,hmain,hbalance,hnorm⟩','ResidueQBalanceDraft.q_balance','theorem graph_power','(hq46 : 46≤q p v)']:
 assert x in s[3],x
assert 'hks,hny⟩' in s[1] and 'hks,hfirst,hmainy⟩' in s[2]
assert '∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y' in s[10]
assert 'theorem y_strictMono (b : V)' in s[11]
# Small standard controls: ordered nonnegative Pell ordinate is strictly
# increasing, and every main coordinate in this list is uniquely identified.
cases=0
for a in range(6):
 x,y=1,0;ys=[]
 for t in range(10):
  assert x*x==1+(a+1)*(a+3)*y*y
  if ys: assert y>ys[-1]
  ys.append(y);x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
  cases+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},
 'generated_sources_exact':True,'small_pell_controls':cases,'lean_executed':False,
 'proof_status':'unelaborated, all graph and provider assumptions inherited'},sort_keys=True,indent=2))
