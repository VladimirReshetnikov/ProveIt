#!/usr/bin/env python3
"""Build the literal 218-state table from the pinned K219 table, without search."""
from pathlib import Path
import argparse,json,sys
from common import *
import check_source218 as source
HERE=Path(__file__).resolve().parent
PATCH_SHA='bb2b2bbd6c404e3f8a0aa59fdd86d49236516c848b702c680fd48d870ff75473'
STAGE_SHA='f29cf17e6e872b479c9ee11b0e6ab3bb94f3f5497143e5fa85d1798db98a7b12'

def construct_table(baseline):
    raw=(baseline/'machine/k219.native.tm').read_bytes();require(sha(raw)==BASE_TABLE_SHA,'Pinned K219 native table differs')
    old=parse_table(raw);stage=old.copy();patch=source.load_pinned('data/stage219_patch.json',PATCH_SHA)
    require(len(patch)==33,'Intermediate decoder patch count')
    for row in patch:
        key=(row['state'],row['read']);require(stage[key]==tuple(row['old']),'Intermediate patch precondition')
        stage[key]=tuple(row['new'])
    require(sha(table_bytes(stage))==STAGE_SHA,'Intermediate 219-state table identity')
    # Expose the right 26-leaf child of the old 52-leaf source role.
    unfolded=stage.copy();require(unfolded[188,0]==(0,1,165) and unfolded[188,1]==(1,1,20),'Old role-188 layout')
    unfolded[188,0]=(0,1,166);unfolded[188,1]=(1,1,12)
    require(unfolded[85,0]==unfolded[212,0]==(0,1,98),'Common read-zero row')
    require(unfolded[85,1]==(1,1,12) and unfolded[212,1]==(1,1,150),'Right-child entries')
    incoming=lambda q:[(k,v)for k,v in unfolded.items()if v[2]==q]
    require(incoming(85)==[((155,0),(0,1,85))],'Native85 entry marker')
    require(incoming(212)==[((177,1),(1,1,212))],'Native212 entry marker')
    final={(q,bit):(w,d,85 if target==212 else target)for(q,bit),(w,d,target)in unfolded.items()if q!=212}
    final[85,1]=(1,-1,190)
    # Literal whole-window decoder blocks. All inspected cells are the marker
    # written by the unique incoming row and the already-known read-one cell.
    alias_traces=[]
    for marker,target in((0,12),(1,150)):
        tape={-1:marker,0:1};original=tape.copy();q=85;h=0;trace=[]
        while (q,h)!=(target,1):
            require(len(trace)<10 and h in tape,'Alias block leaves its two-cell window')
            bit=tape[h];w,d,z=final[q,bit];trace.append([q,h,bit,w,d,z]);tape[h]=w;h+=d;q=z
        require(tape==original,'Alias block changes the tape')
        require(len(trace)==(3 if marker==0 else 5),'Alias block duration')
        alias_traces.append(dict(marker=marker,target=target,trace=trace))
    result=table_bytes(final);require(sha(result)==TABLE_SHA,'Final native table byte identity');parse_table(result)
    states={q for q,bit in final};require(len(states)==218 and len(final)==436,'218-state census')
    reached={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            z=final[q,bit][2]
            if z!=254 and z not in reached:reached.add(z);todo.append(z)
    require(reached==states,'Graph-unreachable working state')
    require({q for q,bit in old}-states=={212} and not states-{q for q,bit in old},'Net state change')
    return old,stage,unfolded,final,alias_traces

def decoder_certificate(table,tree):
    by_path={}
    def walk(node,path=''):
        if source.sl.leaf(node):return
        by_path[path]=node;walk(node[0],path+'0');walk(node[1],path+'1')
    walk(tree);allocation={};maxsteps=0
    for path in sorted(by_path):
        cells={-1:1,**{i:int(bit)for i,bit in enumerate(path)}};initial=cells.copy();q=84;h=0
        for tick in range(10000):
            if h==len(path):break
            require(h in cells and q!=254,'Decoder touches unrepresented exterior')
            w,d,q=table[q,cells[h]];cells[h]=w;h+=d
        else:raise ValueError('Decoder prefix did not terminate')
        require(cells==initial,'Decoder changes its source prefix');maxsteps=max(maxsteps,tick)
        node_sha=sha(source.sl.compact(by_path[path]));allocation.setdefault(q,{}).setdefault(node_sha,[]).append(path)
    roles=sum(len(v)for v in allocation.values());unique={x for v in allocation.values()for x in v};states={q for q,bit in table}
    require((len(allocation),roles,len(unique),len(states-set(allocation)))==(168,183,182,50),'Decoder/source-role accounting')
    return allocation,dict(internal_prefixes=len(by_path),decoder_states=168,decoder_roles=183,source_internal_nodes=182,
        duplicated_logical_roles=1,shared_extra_roles=15,nondecoder_states=50,maximum_prefix_steps=maxsteps)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline','--parent',dest='baseline',type=Path,required=True);ap.add_argument('--sites',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    tree,source_raw,source_receipt=source.construct(a.baseline)
    if a.sites is not None:require(source_raw==a.sites.read_bytes(),'Source construction differs from requested sites')
    old,stage,unfolded,table,traces=construct_table(a.baseline);allocation,counts=decoder_certificate(table,tree)
    a.output.mkdir(parents=True,exist_ok=True);(a.output/'candidate.tm').write_bytes(table_bytes(table));(a.output/'unfolded219.tm').write_bytes(table_bytes(unfolded));(a.output/'sites.json').write_bytes(source_raw)
    (a.output/'intermediate219.tm').write_bytes(table_bytes(stage))
    stage_tree=source.decode_dag(source.load_pinned('data/source205.dag.json',source.DAG_SHA))
    (a.output/'intermediate_sites205.json').write_bytes(source.sl.compact(source.sl.sites(stage_tree)))
    dump(a.output/'allocation.json',allocation);dump(a.output/'source.json',source_receipt);dump(a.output/'source_certificate.json',source_receipt)
    receipt=dict(status='EXACT_K218_CONSTRUCTION_PASS',working_states=218,transition_rows=436,start=0,dispatcher=84,halt=254,
        table_sha256=TABLE_SHA,source_sha256=SOURCE_SHA,baseline_table_sha256=BASE_TABLE_SHA,baseline_source_sha256=BASE_SOURCE_SHA,
        intermediate_table_sha256=STAGE_SHA,removed_states=[212],new_states=[],graph_reachable_states=218,
        changed_retained_rows=[dict(state=q,read=bit,old=old[q,bit],new=v)for(q,bit),v in sorted(table.items())if old[q,bit]!=v],
        alias=dict(kept_state=85,removed_state=212,new_read_one_action=[1,-1,190],blocks=traces,
            hypothesis='Every entry to 85 or 212 writes its origin marker into the immediately preceding cell. Unique incoming rows 155/0 and 177/1 establish this on arbitrary tapes.'),
        source_metrics=source.sl.metrics(tree),**counts,
        scope='Exact syntax, state census, source graph equality, decoder-prefix relation and two-cell alias blocks. Unbounded primitive semantics and blank startup are separate certificates.')
    require(len(receipt['changed_retained_rows'])==32,'Final retained-row patch count');dump(a.output/'construction.json',receipt)
    print(json.dumps({k:v for k,v in receipt.items()if k not in('changed_retained_rows','alias')},indent=2))
if __name__=='__main__':main()
