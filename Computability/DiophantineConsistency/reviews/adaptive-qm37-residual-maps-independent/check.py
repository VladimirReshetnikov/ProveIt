#!/usr/bin/env python3
"""Read-only independent audit of every proposed QM37 residual case."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/adaptive-qm37-residual-maps-draft/AdaptiveQM37ResidualMaps.lean.src','967db1a4348b9110c1eeca74546029c94e7dbd6676e5bf0bd18e591bb758ad73')
pin('research/adaptive-qm37-residual-maps-draft/source-result.json','c3aef1286d29547be6efdaa7c112185a6429d3e8eb48b5cb27cff268a26ab3d6')
pin('research/adaptive-qm37-conditional-model-draft/AdaptiveQM37ConditionalTransfer.lean.src','be810ba3342ba05423e42e70eceff065809ba0380b804b79060b17ae73415566')
pin('research/adaptive-qm37-conditional-model-draft/AdaptiveQM37DifferenceWitness.lean.src','b65647fb73619d6f52e166ae61233854a47e9f968174481f321f44bcdf915c80')
pin('research/adaptive-qm37-conditional-model-draft/AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
pin('research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
pin('reviews/adaptive-square-sums37-independent/result.json','58ba07591199a0ce77fa6c6863390e3f7b72894c0f6d564d41cdc3e86567094c')
def theorem(n):
 m=re.search(r'(?ms)^theorem '+re.escape(n)+r'\b(.*?)(?=^theorem |^end DiophantineConsistency)',s);assert m,n;return m.group(1)
for j in range(28):
 if j in (2,4):continue
 i=j if j<21 else j+1
 t=theorem('same%02d'%j)
 assert f'AdaptiveQM38ResidualsDraft.residuals p {i})' in t,(i,j)
 assert f'AdaptiveQM37ResidualsDraft.residuals p {j})' in t,(i,j)
 assert 'extend v k' in t
for i in (4,21):assert f'AdaptiveQM38ResidualsDraft.residuals p {i})' in theorem('dropped%02d'%i)
a=theorem('aux_relation')
for x in ['AdaptiveQM38ResidualsDraft.residuals p 2)', 'AdaptiveQM37ResidualsDraft.residuals p 2)', 'ι (v 30) *', 'AdaptiveQM37ResidualsDraft.residuals p 4)']:assert x in a,x
assert 'extend (project v d)=v' in theorem('extend_project')
assert 'v 11*v 11=v 25*v 25+d' in theorem('project_difference')
assert 'linear_combination -h' in theorem('project_difference')
def branches(n):
 t=theorem(n); assert 'fin_cases i' in t
 return re.split(r'(?m)^  · ',t.split('fin_cases i',1)[1])[1:]
b=branches('extend_zero');assert len(b)==29,len(b)
for i,x in enumerate(b):
 if i in (4,21): assert f'dropped{i:02d} p v' in x
 elif i==2: assert all(y in x for y in ('aux_relation p v','hd, mul_zero, add_zero','hc 2'))
 else:
  j=i if i<21 else i-1
  assert f'same{j:02d} p v' in x and f'hc {j}' in x,(i,j)
c=branches('project_zero');assert len(c)==28,len(c)
for j,x in enumerate(c):
 if j==4: assert 'exact hdiff' in x
 else:
  i=j if j<21 else j+1
  assert f'AdaptiveQM38ResidualsDraft.residuals p {i})' in x and f'using hp {i}' in x,(i,j)
  if j==2:assert 'aux_relation p (project v d)' in x and 'hdiffR' in x
  else:assert f'same{j:02d} p (project v d)' in x,(i,j)
g=theorem('graphZeroObligations')
assert 'project_zero' in g and 'extend_zero' in g
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',s)
print(json.dumps({'scope':'static branch and source audit only; no Lean elaboration or iPRA proof','common_residual_lemmas':26,'parent_zero_cases':len(b),'child_zero_cases':len(c),'dropped_parent_residuals':[4,21],'special_auxiliary':[2,4],'finite_case_order_assumed':True,'prior_qm38_obligation_unsolved':True},sort_keys=True,indent=2))
