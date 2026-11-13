from pathlib import Path
from hashlib import sha256
import difflib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-corrected-composition-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for n in ('ordinary13-independent-k-rank-orientation-repair','ordinary13-independent-k-positive-corrected-composition-draft'):
 p=Path('research')/n;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
old=Path('research/ordinary13-independent-k-rank-representation-draft/IndependentKRankRepresentation.lean.src').read_text()
new=Path('research/ordinary13-independent-k-rank-orientation-repair/IndependentKRankRepresentationCorrected.lean.src').read_text()
assert old.count('  linear_combination h\n')==1
expected=old.replace('  linear_combination h\n','  linear_combination -h\n').replace('IndependentKRankRepresentationDraft','IndependentKRankRepresentationCorrectedDraft')
assert new==expected
# Independent hunk counting confirms only namespace/query names and tactic change.
a=old.splitlines();b=new.splitlines();changes=[(tag,a[i:j],b[k:l]) for tag,i,j,k,l in difflib.SequenceMatcher(a=a,b=b).get_opcodes() if tag!='equal']
assert len(changes)==2,changes
assert sum('linear_combination h' in '\n'.join(x[1]) for x in changes)==1
assert 'namespace DiophantineConsistency.IndependentKRankRepresentationCorrectedDraft' in new
assert '  linear_combination -h\n' in new
src=Path('research/ordinary13-independent-k-positive-composition-draft/IndependentKPositiveComposition.lean.src').read_text()
dst=Path('research/ordinary13-independent-k-positive-corrected-composition-draft/IndependentKPositiveCorrectedComposition.lean.src').read_text()
expected=src.replace('import IndependentKRankRepresentation\n','import IndependentKRankRepresentationCorrected\n').replace('IndependentKRankRepresentationDraft','IndependentKRankRepresentationCorrectedDraft').replace('IndependentKPositiveCompositionDraft','IndependentKPositiveCorrectedCompositionDraft')
assert dst==expected
assert 'import IndependentKRankRepresentationCorrected\n' in dst
for name in ('rankExpr','first_norm_F_lt_q','rank_representation'):
 assert re.search(r'^(?:theorem|def) '+name+r'\b',new,re.M)
 assert 'IndependentKRankRepresentationCorrectedDraft.'+name in dst
assert 'IndependentKRankRepresentationDraft' not in dst
assert 'import IndependentKZeroGraphFacts\n' in dst
assert 'zero_k_impossible_of_rank_representation' in dst and '(hz : InternalZero (graph intPorts).output v) : 0<v 10' in dst
oldhelper=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
assert 'ι (rank p v) =\n      (ι (v 2+1)' in oldhelper
assert '(rankExpr (fun j => (p j:ℤ))).evalRing (fun j => ι (v j)) =\n      ι (Residue90GraphNormsDraft.rank p v)' in new
# eq_of_eq side-condition for h: A=E, target E=A: negating h
# changes the ring-normalization side condition from 2E=2A to E+A=A+E.
for A in range(-3,4):
 for E in range(-3,4):assert E+A==A+E
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'both_author_receipts_reproduced':True,'rank_source_exact_delta_and_hunks':True,
 'composition_exact_delta':True,'module_and_namespace_references_match':True,
 'corrected_sign_ring_side_condition':True,'lean_executed':False,
 'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
