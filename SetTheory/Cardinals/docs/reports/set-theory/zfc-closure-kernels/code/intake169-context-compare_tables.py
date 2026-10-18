#!/usr/bin/env python3
"""Own static table comparison only. No transition execution or supplied imports."""
from pathlib import Path
import hashlib, json
R=Path('/tmp/zfc-compare-d584512002')
A=R/'zfc242-context-reuse-20261018/zfc242-context-reuse-20261018'
B=R/'zfc242-contextual-reuse-20261018/zfc242-contextual-reuse-20261018'
OLD=Path('/tmp/zfc-intake-8c41b1fb7d')
P=OLD/'BusyBeaver_242_Research_2026-10-18/busybeaver242-research/runtime'
Q=OLD/'BusyBeaver_241_Companion_2026-10-18/busybeaver241-companion/runtime'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
def parse(p):
    t={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R')
        t[q,b]=(w,d,n)
    s={q for q,b in t};assert set(t)=={(q,b)for q in s for b in(0,1)}
    return t
paths=[A/'reference/zfc_combined243_old.tm',A/'machine/zfc_context242_old.tm',B/'machine/zfc_return_fold242_old.tm',P/'survivor_1_old.tm',P/'survivor_1.tm',B/'machine/zfc_return_fold242.tm',Q/'candidate_1_old.tm']
base,delete15,delete27,primary,pcanon,bcanon,current241=map(parse,paths)
assert delete27==primary and paths[2].read_bytes()==paths[3].read_bytes()
assert pcanon==bcanon
assert paths[5].read_text()=='#! start 0\n'+paths[4].read_text()
rename=lambda q:27 if q==15 else q
renamed={(rename(q),b):(w,d,rename(n))for(q,b),(w,d,n)in primary.items()}
assert renamed==delete15 and len(renamed)==484
def delta(old,new):
    return dict(deleted_states=sorted({q for q,b in old}-{q for q,b in new}),changed=[dict(row=list(k),old=list(old[k]),new=list(v))for k,v in sorted(new.items())if old[k]!=v])
assert delta(base,delete15)['deleted_states']==[15]
assert delta(base,delete27)['deleted_states']==[27]
foldpatch={(17,0):(0,'L',106),(17,1):(1,'L',37),(46,0):(0,'R',17),(50,0):(0,'R',17)}
def fold39(t):
    out={k:v for k,v in t.items()if k[0]!=39};out.update(foldpatch)
    assert all(v[2]!=39 for v in out.values());return out
assert fold39(primary)==current241
assert fold39(delete15)=={(rename(q),b):(w,d,rename(n))for(q,b),(w,d,n)in current241.items()}
incoming=lambda t,q:sorted([s,b,w,d]for(s,b),(w,d,n)in t.items()if n==q)
for t in(primary,delete15):
    assert incoming(t,17)==[[12,1,1,'R']]
    assert incoming(t,39)==[[46,0,0,'R'],[50,0,0,'R']]
blockrows=[(17,0),(106,1),(92,0),(107,1),(125,0),(17,1),(37,1),(55,0),(106,0),(93,0),(37,0),(25,0)]
assert all(fold39(primary)[k]==fold39(delete15)[k]for k in blockrows)
record=dict(status='STATIC_LITERAL_AND_SOURCE_COMPARISON_COMPLETE',reviewer_role='Author of pending Fold241 Lean sources; independent reader of these delivered reports; no proof/tool execution.',inputs=[desc(p)for p in paths],patches={'context_reuse':delta(base,delete15),'contextual_reuse':delta(base,delete27)},contextual_primary_inherited_byte_identical=True,contextual_canonical_diff_only_start_header=True,context_primary_exact_state_isomorphism='rename retained state15 to27 in primary242A; every one of484rows agrees',fold39_result='current241 and alternative241 are exact state isomorphisms under the same rename; no240 saving',fold39_incoming={'17':incoming(primary,17),'39':incoming(primary,39)},fold39_all12_distinct_block_rows_unchanged=True,source_only=True,supplied_execution=False,script=desc(__file__))
(R/'drop-review/table-comparison.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(desc(R/'drop-review/table-comparison.json')))
