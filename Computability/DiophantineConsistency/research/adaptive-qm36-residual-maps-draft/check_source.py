#!/usr/bin/env python3
"""Read-only residual-index/source checks; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];B=D/'research/adaptive-qm36-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','6ce538aa98b73d7cd39ae4ca3ec87df411aaeea3d458a284b254e43fe391a592');obs=json.loads(pin(P/'result.json','e2be956afcafb6a217d4cfd230f8b09156d6a84f2bc8c5b3fe13a8c341a529f6'))
proof=pin(P/'AdaptiveQM36ResidualMaps.lean.src','7fbe29e233c55aa8a3da52ec62030e294d523d4cc820a3ea24195c6926b82432')
a=pin(D/'research/adaptive-qm37-conditional-model-draft/AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
b=pin(B/'AdaptiveQM36Residuals155.lean.src','03c99c18fc52e185bf8c334ce3ab62afb40c9f0d91d7bdc2cd5e695263dfae95')
pin(B/'AdaptiveQM36ParentSlots.lean.src','69bf3f920031a0451740b04c48a68a3ee4edd5708aed84cf85066bf24a23ac78');pin(B/'AdaptiveQM36ConditionalTransfer.lean.src','865a63bdcb03a5f7dc1845bc5af0217529b3d549e7a6e67b73f0f1cf447bc754')
cert=json.loads(pin(D/'research/adaptive-square-sums36-combined-shift-quartic/result.json','02813e0ec93140504bbc9f18578acb7c2b3ad1eb12be9767db676196c9c0c7ef'))
def vec(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
pa=vec(a);ch=vec(b);assert len(pa)==28 and len(ch)==27 and pa[11]=='productDifference' and pa[26]=='gammaProductDifference' and ch[11]=='combinedEquality' and pa[15]==ch[15]=='dDifference'
expected=[(pa.index(n),j,n) for j,n in enumerate(ch) if j not in (11,15)]
actual=re.findall(r'/-- Parent residual (\d+), child residual (\d+): ([A-Za-z0-9_]+)\. -/',proof);assert [(int(i),int(j),n) for i,j,n in actual]==expected and len(expected)==25
for i,j,n in expected:
 assert f'theorem same{j:02d}' in proof and f'(AdaptiveQM37ResidualsDraft.residuals p {i}).evalRing' in proof and f'(AdaptiveQM36Residuals155Draft.residuals p {j}).evalRing' in proof
for n in ('dropped11','dropped26','d_relation','extend_project','project_combined','extend_zero','project_zero','graphZeroObligations'):assert 'theorem '+n in proof
assert '((p 0 : ℤ) : DiffRing V)=ι beta' in proof and '(3+4*(ι (v 28)+ι (v 7)))' in proof
assert cert['parent_d_equals_child_d_plus_H_times_combined_residual'] and obs['common_residual_pairs']==25
print(json.dumps({'scope':'bounded text/index checks and external residual observation only; no Lean/model proof','common_residual_pairs':25,'dropped_parent_residuals':[11,26],'child_combined_residual':11,'special_d_residual':15,'represented_beta_cast_explicit':True,'proofs_unelaborated':True},indent=2,sort_keys=True))
