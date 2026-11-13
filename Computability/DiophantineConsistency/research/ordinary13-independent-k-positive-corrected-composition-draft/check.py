from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-positive-corrected-composition-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for n in ('ordinary13-independent-k-positive-composition-draft','ordinary13-independent-k-rank-orientation-repair'):
 p=Path('research')/n;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
p=Path('research/ordinary13-independent-k-positive-composition-draft/IndependentKPositiveComposition.lean.src');s=p.read_text()
s=s.replace('import IndependentKRankRepresentation\n','import IndependentKRankRepresentationCorrected\n').replace('IndependentKRankRepresentationDraft','IndependentKRankRepresentationCorrectedDraft').replace('IndependentKPositiveCompositionDraft','IndependentKPositiveCorrectedCompositionDraft')
c=(D/'IndependentKPositiveCorrectedComposition.lean.src').read_text();assert c==s
r=Path('research/ordinary13-independent-k-rank-orientation-repair/IndependentKRankRepresentationCorrected.lean.src').read_text()
assert 'namespace DiophantineConsistency.IndependentKRankRepresentationCorrectedDraft' in r
for name in ('rankExpr','first_norm_F_lt_q','rank_representation'):
 assert re.search(r'^(?:def|theorem) '+name+r'\b',r,re.M),name
 assert 'IndependentKRankRepresentationCorrectedDraft.'+name in c,name
assert 'IndependentKRankRepresentationDraft' not in c and 'import IndependentKRankRepresentation\n' not in c
assert 'import IndependentKZeroGraphFacts\n' in c and 'zero_k_impossible_of_rank_representation' in c
print(json.dumps({'source_delta_only_import_and_namespaces':True,'corrected_provider_module_and_declarations_match':True,'prior_composition_and_repair_receipts_reproduced':True,'lean_executed':False,'elaboration_provider_or_axiom_validation':False},sort_keys=True,indent=2))
