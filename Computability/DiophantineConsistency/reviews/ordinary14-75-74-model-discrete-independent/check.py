#!/usr/bin/env python3
"""Independent source-interface/model-lemma audit, never invokes Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-75-74-model-discrete-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'a9d1ea4c8388477457cc9b21065b39540f3f1293a984d44c94f31055ea5abe3f','ModelDiscrete75To74.lean':'2154e4c72f347b48ace2b73e98782b64d87e274c8f4b2b2b6379de054ad4f404','check_source.py':'1d52a69e9a53b3c50724134bafe4930a660f3cdedc7e2ed2b3ec60e9e3abebaa','observation.json':'3568390933b18c445096ec14860911a313996cfb1e8bb559b8acd85e7f63b6b5'}
tail=b"\nIndependent source review: [75/74 model discreteness](../../reviews/ordinary14-75-74-model-discrete-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='7b241b720394f971a725742375bb5ce154d3db3dd44024eac6b554880a9e4309'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'ModelDiscrete75To74.lean').read_text();eq=D/'research/ordinary14-75-74-model-equivalence-draft/ModelEquivalence75To74.lean';dif=D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean';model=D/'Lean/DiophantineConsistency/ModelArithmetic.lean'
for p,h in [(eq,'d0b87479f1370ee5c1d9510a94258fabd333f8b64d01e479aa66230a1c3c42ac'),(dif,'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'),(model,'2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6')]:assert sha(p)==h
assert s.splitlines()[0]=='import ModelEquivalence75To74' and not re.search(r'^import .*ModelArithmetic',s,re.M)
for t in ['theorem difference_ring_discrete : Discrete (DiffRing V)','one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hx','(hb : 0<beta) (hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)','positive_zero_iff p beta K difference_ring_discrete hb hbeta hK','positive_zero_iff_natural_ports p difference_ring_discrete hb']:
 assert t in s,t
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
assert 'theorem one_le_of_pos (hd : ∀ a : V, 0 < a → 1 ≤ a) {x : DiffRing V} (hx : 0 < x) : 1 ≤ x' in dif.read_text()
for t in ['theorem model_one_le (a : V) (h : 0 < a) : 1 ≤ a := pos_iff_one_le.mp h','theorem model_discrete : Discrete (DiffRing V) := fun _ hx => one_le_of_pos model_one_le hx']:
 assert t in model.read_text()
t=eq.read_text()
for x in ['(hd : Discrete (DiffRing V)) (hb : 0<beta)','(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)','(p : Fin 4 → ℕ)','P72Root.cast_port p 0','P72Root.cast_port p 1']:
 assert x in t,x
review=D/'reviews/ordinary14-75-74-model-equivalence-independent'
assert sha(review/'check.py')=='4e44f129fc78ef8cab3cace130d1b8ef58a293adad5ccdc867964e0879458e45'
assert sha(review/'observation.json')=='6c8630c0f816285bf2e85aa05b8682f092ea6ee2f3f4fa71afdb91d7c5433d78'
assert subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],cwd=D,check=True,capture_output=True).stdout==(review/'observation.json').read_bytes()
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interfaces only; no Lean, object/provider coherence or endpoint proof','author_pins':pins,'wrapper_sha256':sha(eq),'difference_ring_sha256':sha(dif),'model_arithmetic_sha256':sha(model),'prior_wrapper_review_replayed':True,'author_receipt_reproduced':True},sort_keys=True,indent=2))
