from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-first-rank-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'IndependentKFirstRank.lean.src').read_text()
assert s.startswith('import IndependentKZeroMainRank\n')
names=['rank_window_of_coefficient','first_norm_coefficient','zero_k_impossible']
for n in names:
 assert len(re.findall(r'^theorem '+n+r'\b',s,re.M))==1
 assert '#print axioms DiophantineConsistency.IndependentKFirstRankDraft.'+n in s
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
for token in ['by_cases hc : 0<C','mul_self_eq_mul_self_iff.mp hnorm\'',
 'have hrzero : r=0','have hP_eq : P= -B','have hGid',
 'have hR := rank_window_of_coefficient','IndependentKZeroMainRankDraft.zero_k_impossible',
 '(hrank : (ι R : DiffRing V)=','(hfirst : let b : DiffRing V',
 '(hshape : let a:=X*Y+Y','(hnorm : let a:=X*Y+Y']:
 assert token in s,token
up=Path('research/ordinary13-independent-k-zero-main-rank-draft/IndependentKZeroMainRank.lean.src').read_text()
assert 'theorem zero_k_impossible (q X Y s R eta gamma : V) (z : DiffRing V)' in up
assert '(hq : 0<q) (hs : 0<s) (hY : Y=q^3*s) (hR : R+1<q^4)' in up
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'three_declared_drafts_and_axiom_queries_observed':True,
 'branch_and_conditional_main_helper_call_observed':True,
 'bounded_lexical_proof_escape_scan_clear':True,
 'lean_executed':False,'elaboration_or_provider_validation':False},indent=2,sort_keys=True))
