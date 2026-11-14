#!/usr/bin/env python3
"""Check every frozen search input, source hash, and counted-cycle ledger.

This is an input and provenance checker, not a proof of TM correctness.
"""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
D=json.loads((P/'search_summary.json').read_text())
checked={}
for r in D['runs']:
 for field in ['input','source']:
  data=(P/r[field]).read_bytes()
  assert hashlib.sha256(data).hexdigest()==r[field+'_sha256'],r['run']
 assert r['counted_iteration_slots']==3000*r['replay_cycles']
 fn=r['input']
 if fn in checked:continue
 lines=(P/fn).read_text().splitlines();nt,nw,np,nrows=map(int,lines[0].split())
 assert (nt,nw,np,nrows)==(11,190,189,268)
 terms=[list(map(int,x.split()))for x in lines[1:1+nt]]
 assert all(len(t)==6 for t in terms)
 start=1+nt
 rows=[list(map(int,x.split()))for x in lines[start:start+nrows]]
 assert len({tuple(x[:2])for x in rows})==268
 states={x[0]for x in rows};assert len(states)==134
 assert {tuple(x[:2])for x in rows}=={(q,b)for q in states for b in [0,1]}
 assert all(b in [0,1]and w in [0,1]and d in [0,1]for q,b,w,d,n in rows)
 start+=nrows
 shape=[tuple(map(int,x.split()))for x in lines[start:start+np]]
 for j,(a,b)in enumerate(shape):assert 0<=a<nw+j and 0<=b<nw+j
 def leaves(i):return[i]if i<nw else leaves(shape[i-nw][0])+leaves(shape[i-nw][1])
 assert leaves(nw+np-1)==list(range(nw)),fn
 vectors=[]
 for x in lines[start+np:]:
  vs=list(map(int,x.split()));assert len(vs)==1+vs[0];assert all(0<=v<nt for v in vs[1:]);vectors.append(vs[1:])
 assert len(vectors)==76
 prefix,suffix,gate0,gate1=vectors[:4];heads=vectors[4:]
 default_word=prefix+sum([heads[j*12]for j in range(6)],[])+gate0+suffix
 assert len(default_word)==190
 # Every head variant has the same length as its base; all orders therefore
 # preserve the 190 terminal positions expected by the binary tree.
 assert len(gate0)==len(gate1)
 for j in range(6):assert len({len(x)for x in heads[j*12:j*12+12]})==1
 checked[fn]={'fixed_controls':134,'macro_positions':190,'tree_nodes':189,'ordered_leaf_positions':True}
assert sum(x['counted_iteration_slots']for x in D['runs'])==D['counted_iteration_slots']==90819000
assert D['best_state_score']==194 and not D['verified_sub194_machine']
receipt={'status':'PASS','runs':len(D['runs']),'unique_inputs':len(checked),'counted_iteration_slots':D['counted_iteration_slots'],'best_state_score':194,'checks':checked}
(P/'evidence/input_check.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k]for k in ['status','runs','unique_inputs','counted_iteration_slots','best_state_score']},indent=2))
