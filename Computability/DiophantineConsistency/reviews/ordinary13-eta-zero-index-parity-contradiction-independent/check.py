#!/usr/bin/env python3
"""Independent full hypothesis transcription and parity direction audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src','a5aac5250b0b4c05fa765ed1013e5287706f038ea60e5083d9c4cba4025e0e74')
pin('research/ordinary13-eta-zero-index-parity-contradiction-draft/result.json','0915ac9a9e1ecbdc6561f3b9123423594881bda94683c1a1298df7b500da0fbf')
p=pin('research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src','b02fbec88cc6fbf58651346920fd9626790e623c79bdcb5c2f73f4ff68e88f63')
y=pin('research/pell-main-ordinate-parity-model-draft/PellOrdinateParity.lean.src','bb0e98110be0d3c091c6d00c6b72a60232dfd17cd1d673fdce6cf6617ef189b1')
pin('reviews/ordinary13-eta-zero-p72-index-independent/result.json','ec1c18cc6c5ab476e044a320fd25bdbfee7b42dd66cde17bb403e442c9e0096e')
pin('reviews/pell-main-ordinate-parity-model-independent/result.json','7b674d2a3a18738c70720f40ed0878680f3b152e5396b6ebd2efde89944ee6c2')
a=p.split('theorem indices_ordinary',1)[1].split(' :\n    13 ≤ n',1)[0]
a=a.replace(' μ m η : V)',' μ m : V)').replace('(hc : c = η + Y * k)','(hc : c = Y * k)')
b=s.split('theorem eta_zero_contradiction',1)[1].split(' :\n    False',1)[0]
assert a==b
for x in ['P72ExactEtaNaturalDraft.indices_ordinary','q X Y k R g c a y0 i\' f T u n s μ m 0','hR26 hny hks hRμ hnmod hmy hg hs\' haux','(R + 1) % 2 = 0','have hRodd : R % 2 = 1','have hcdiv : (2 : V) ∣ c','PellOrdinateParityModelDraft.ordinate_mod_two m a','exact _root_.one_ne_zero (hcodd.symm.trans hceven)']:
 assert x in s,x
assert 'ycoord n b % 2 = n % 2' in y
# Bounded parity direction controls, not a proof for all model indices.
for n in range(1,100):
 R=2*n-1;assert (R+1)%2==0 and R%2==1
 for Y in range(12):
  for t in range(12):
   k=2*t;c=Y*k
   assert c%2==0 and c%2!=R%2
print(json.dumps({'scope':'full eta-zero P72 hypothesis transcription and parity composition; no Lean','only_eta_zero_substitution':True,'all_norm_strong_auxiliary_index_hypotheses_retained':True,'R_odd_c_even_conflict':True,'graph_extraction_and_provider_proofs_open':True,'lean_elaborated':False},sort_keys=True,indent=2))
