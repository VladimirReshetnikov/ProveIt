from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-rank-orientation-repair')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-rank-representation-draft');assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(p/'IndependentKRankRepresentation.lean.src').read_text();assert s.count('  linear_combination h\n')==1
s=s.replace('  linear_combination h\n','  linear_combination -h\n').replace('IndependentKRankRepresentationDraft','IndependentKRankRepresentationCorrectedDraft')
assert s==(D/'IndependentKRankRepresentationCorrected.lean.src').read_text()
old=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
assert 'ι (rank p v) =' in old
assert '(rankExpr (fun j => (p j:ℤ))).evalRing (fun j => ι (v j)) =' in s
assert 'ι (Residue90GraphNormsDraft.rank p v)' in s
print(json.dumps({'source_and_namespace_delta_exact':True,'opposed_helper_and_goal_equalities_observed':True,'original_receipt_reproduced':True,'lean_executed':False,'elaboration_provider_or_axiom_validated':False},sort_keys=True,indent=2))
