"""Self-authored exact table/renumbering and two independent whole-blank simulations.
Supplied artifacts are parsed only as data. No downloaded program is run/imported.
"""
from pathlib import Path
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
import independent_runtime as r
ROOT=Path(__file__).resolve().parent.parent;S=ROOT/'sources'
BASE=ROOT/'prior/zfc_routing245_old.tm'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
op=S/'candidate-combined243__zfc_combined243_old.tm';cp=S/'candidate-combined243__zfc_combined243.tm'
assert sha(op)=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
assert sha(cp)=='a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791'
assert sha(BASE)=='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
base=r.table(BASE);new=r.table(op);canon=r.table(cp);qt=r.table(S/'candidate-rotation244__zfc_rotation244_old.tm')
patch={(12,0):(0,1,18),(12,1):(1,1,17),(17,1):(0,-1,20),(92,1):(1,1,66),(104,1):(1,1,92),(106,1):(1,1,92),(167,1):(1,-1,151)}
assert set(base)-set(new)=={(q,b) for q in (26,122) for b in (0,1)}
assert {k:v for k,v in new.items() if base[k]!=v}==patch
assert len(new)==486 and len(set(q for q,b in new))==243
assert {t for w,d,t in new.values()}-set(q for q,b in new)=={254}
assert not {26,122}&{t for w,d,t in new.values()}
renraw=json.loads((S/'candidate-combined243__renumbering.json').read_text())
ren={int(k):v for k,v in renraw['old_to_canonical'].items()};inv=dict(enumerate(renraw['canonical_to_old']))|{243:254}
assert inv=={v:k for k,v in ren.items()} and ren[95]==0 and ren[96]==87 and ren[254]==243
assert set(inv)==set(range(244)) and len(ren)==244
assert canon=={(ren[q],b):(w,d,ren[t]) for (q,b),(w,d,t) in new.items()}
assert set(qt)-set(new)=={(122,0),(122,1)}
qtpatch={(12,0):(0,1,18),(12,1):(1,1,17),(17,1):(0,-1,20)}
assert qt=={k:qtpatch.get(k,v) for k,v in base.items() if k[0]!=26}
ones=set();q=95;h=0;visited=set()
for tick in range(407967):
 b=int(h in ones);w,d,t=new[q,b];visited.add((q,b))
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=t
assert (q,h)==(96,-5)
seed=[3,0,0,0,3,0,0,0,0];want={v-5 for v in r.frame('',seed,[1]*167,117)}
assert ones==want and len(ones)==351
# Separate dense tape, canonical table, automatic growth, blank outside.
arr=bytearray(1);left=0;head=0;state=0
for tick in range(407967):
 if head<left:arr=bytearray(left-head)+arr;left=head
 if head>=left+len(arr):arr.extend(bytearray(head-left-len(arr)+1))
 w,d,state=canon[state,arr[head-left]];arr[head-left]=w;head+=d
dense={left+i for i,b in enumerate(arr) if b}
assert (state,head,dense)==(87,-5,want)
result={'status':'EXACT_TABLE_AND_WHOLE_BLANK_PASS','canonical_sha256':sha(cp),'old_sha256':sha(op),'baseline_sha256':sha(BASE),'working_states':243,'rows':486,'retained_rows_changed':len(patch),'retained_rows_unchanged':479,'removed_states':[26,122],'literal_patches_commute':True,'renumbering_bijective':True,'blank_transitions':407967,'blank_sparse_old_and_dense_canonical_agree':True,'root_frame':{'old_state':96,'canonical_state':87,'head':-5,'marker':-6,'header':176,'span':181,'logical_registers':seed,'spare_count':167,'spare_values':1,'ones':351,'zero_elsewhere':True},'boot_rows_used':len(visited),'scope':'Exact finite startup and literal table facts; source/runtime and halting interpretation are separate obligations.'}
(ROOT/'independent-runtime/table_and_boot.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
