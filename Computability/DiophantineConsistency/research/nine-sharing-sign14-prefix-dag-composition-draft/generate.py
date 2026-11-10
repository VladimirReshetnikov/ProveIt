#!/usr/bin/env python3
"""Source-only fragment and DAG-encoding lemma generator."""
import json
from pathlib import Path
here=Path(__file__).resolve().parent;data=here.parent/'nine-sharing-sign14-prefix-dag-fragments';m=json.loads((data/'manifest.json').read_text());assert len(m['fragments'])==29 and len(m['shared'])==44 and len(m['rows'])==5
ops={'+':'add','-':'sub','*':'mul'};ports={'B':0,'K':1,'C':2,'F':3};nums={'1':'one','2':'two','3':'three','4':'four'}
def code(s,i=0):
 c=s[i];i+=1
 if c in ops:
  a,i=code(s,i);b,i=code(s,i);return f'(Code.{ops[c]} ({a}) ({b}))',i
 if c in ports:return f'Code.port {ports[c]}',i
 if c in nums:return f'Code.{nums[c]}',i
 assert 'a'<=c<='o';return f'Code.var {ord(c)-97}',i
header='''/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
'''
for block in range(6):
 imp='Sign14PrefixCodeRow04' if block==0 else f'Sign14PrefixDagFragments{block-1:02}'
 out=f'import DiophantineConsistency.{imp}\n\n'+header;indices=list(range(block*5,min(block*5+5,29)))
 for i in indices:
  fn=m['fragments'][i]['file'];data_s=(data/fn).read_text();term,end=code(data_s);assert end==len(data_s)
  out+=f'def fragment{i:03} : List Char := (include_str "{fn}").toList\ntheorem fragment{i:03}_eq : fragment{i:03} = encode ({term}) := by rfl\n\n'
 out+='end DiophantineConsistency.Sign14PrefixDag\n'
 for i in indices:out+=f'#print axioms DiophantineConsistency.Sign14PrefixDag.fragment{i:03}_eq\n'
 (here/f'Sign14PrefixDagFragments{block:02}.lean').write_text(out)
def render(node):
 if node[0]=='frag':return f'fragment{node[1]:03}'
 if node[0]=='ref':return f'shared{node[1]:02}Bytes'
 return f"('{node[1]}' :: ({render(node[2])} ++ {render(node[3])}))"
def deps(node):
 if node[0]=='frag':return [f'fragment{node[1]:03}_eq']
 if node[0]=='ref':return [f'shared{node[1]:02}Bytes_eq']
 return deps(node[2])+deps(node[3])
for block in range(9):
 imp='Sign14PrefixDagFragments05' if block==0 else f'Sign14PrefixDagShared{block-1:02}'
 indices=list(range(block*5,min(block*5+5,44)));out=f'import DiophantineConsistency.{imp}\n\n'+header
 for i in indices:
  n=m['shared'][i];out+=f'def shared{i:02}Bytes : List Char := {render(n)}\n'
  rules=', '.join(dict.fromkeys(deps(n)))
  out+=f'theorem shared{i:02}Bytes_eq : shared{i:02}Bytes = encode Sign14PrefixCode.shared{i:02} := by\n  unfold shared{i:02}Bytes\n  simp only [{rules}] <;> rfl\n\n'
 out+='end DiophantineConsistency.Sign14PrefixDag\n'
 for i in indices:out+=f'#print axioms DiophantineConsistency.Sign14PrefixDag.shared{i:02}Bytes_eq\n'
 (here/f'Sign14PrefixDagShared{block:02}.lean').write_text(out)
for i,node in enumerate(m['rows']):
 imp='Sign14PrefixDagShared08' if i==0 else f'Sign14PrefixDagRow{i-1:02}'
 out=f'import DiophantineConsistency.{imp}\n\n'+header
 out+=f'def row{i:02}Bytes : List Char := {render(node)}\n';rules=', '.join(dict.fromkeys(deps(node)))
 out+=f'theorem row{i:02}Bytes_eq : row{i:02}Bytes = encode Sign14PrefixCode.row{i:02} := by\n  unfold row{i:02}Bytes\n  simp only [{rules}] <;> rfl\n\nend DiophantineConsistency.Sign14PrefixDag\n#print axioms DiophantineConsistency.Sign14PrefixDag.row{i:02}Bytes_eq\n'
 (here/f'Sign14PrefixDagRow{i:02}.lean').write_text(out)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','fragments':29,'shared':44,'rows':5}))
