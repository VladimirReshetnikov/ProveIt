#!/usr/bin/env python3
"""Own finite publication preparation: literal recipes and reversible dense renaming."""
from pathlib import Path
import json,hashlib
import source_language as s
import build221 as b
P=Path(__file__).resolve().parent
K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k216')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=P/'held-publication';out.mkdir(exist_ok=False)
old=s.tree(json.loads((K/'sites216.json').read_text()));new=s.tree(json.loads((P/'sites-210.json').read_text()))
nodes=[];ids={}
def intern(n):
 if n in ids:return ids[n]
 enc=n if s.leaf(n)else(intern(n[0]),intern(n[1]))
 ids[n]=len(nodes);nodes.append(enc);return ids[n]
oldroot=intern(old);oldcount=len(nodes);newroot=intern(new)
recipe={'parent_source_sha256':sha(K/'sites216.json'),'parent_root':oldroot,'parent_nodes':oldcount,'new_nodes':nodes[oldcount:],'candidate_root':newroot,'candidate_source_sha256':sha(P/'sites-210.json')}
(out/'dag_recipe.json').write_text(json.dumps(recipe,indent=2)+'\n')
T=b.read_table((K/'k216.native.tm').read_bytes());N=b.read_table((P/'allocation210-run2/candidate.native.tm').read_bytes());states=sorted({q for q,_ in N});m={q:i for i,q in enumerate(states)};m[254]=215
assert len(states)==215 and m[0]==0
D={(m[q],bit):(w,d,m[z])for(q,bit),(w,d,z)in N.items()}
assert set(q for q,_ in D)==set(range(215)) and set(z for w,d,z in D.values())-set(range(215))=={215}
assert {(states[q],bit):(w,d,254 if z==215 else states[z])for(q,bit),(w,d,z)in D.items()}==N
(out/'k215.tm').write_bytes(b.table_bytes(D));(out/'k215.native.tm').write_bytes(b.table_bytes(N));(out/'sites215.json').write_bytes((P/'sites-210.json').read_bytes())
recipe={'parent_native_sha256':sha(K/'k216.native.tm'),'candidate_native_sha256':sha(out/'k215.native.tm'),'removed_states':sorted(set(q for q,_ in T)-set(states)),'replacement_rows':[[q,bit,w,'R'if d==1 else'L',z]for(q,bit),(w,d,z)in sorted(N.items())if T.get((q,bit))!=(w,d,z)],'native_serialization_order':states}
(out/'table_recipe.json').write_text(json.dumps(recipe,indent=2)+'\n')
canon={'native_sha256':sha(out/'k215.native.tm'),'canonical_sha256':sha(out/'k215.tm'),'native_to_canonical':m,'canonical_to_native':{v:k for k,v in m.items()},'start_native':0,'start_canonical':0,'halt_native':254,'halt_canonical':215,'status':'EXACT_REVERSIBLE_TABLE_ISOMORPHISM_PASS','method':'ascending native working-state labels, terminal215'}
(out/'canonicalization.json').write_text(json.dumps(canon,indent=2)+'\n')
print(json.dumps({'status':'HELD_RECIPES_AND_CANONICALIZATION_PASS','states':215,'rows':430,'added_dag_recipe_nodes':len(nodes)-oldcount,'replaced_rows':len(recipe['replacement_rows']),'files':{p.name:sha(p)for p in out.iterdir()}},indent=2))
