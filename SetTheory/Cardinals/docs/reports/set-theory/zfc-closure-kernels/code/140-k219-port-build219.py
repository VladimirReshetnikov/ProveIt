#!/usr/bin/env python3
"""Exact eight-row construction from the pinned K220 table; no optimizer."""
from pathlib import Path
import argparse,json,sys
from common import *
import build_source219 as source
PATCH={(87,0):(0,1,301),(87,1):(1,1,21),(88,0):(0,1,122),
       (103,0):(0,1,108),(103,1):(0,-1,302),(108,1):(0,-1,10),
       (113,0):(0,-1,302),(198,0):(1,-1,40)}
NEW={(301,0):(0,1,45),(301,1):(1,1,103),
     (302,0):(0,-1,4),(302,1):(0,-1,302)}
DELETE={102,120,121}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    oldraw=(a.baseline/'machine/k220.native.tm').read_bytes();oldsource=(a.baseline/'machine/sites220.json').read_bytes()
    require(sha(oldraw)==BASE_TABLE_SHA and sha(oldsource)==BASE_SOURCE_SHA,'Pinned K220 inputs differ')
    old=parse_table(oldraw);oldtree=source.parse(json.loads(oldsource));occurrences=[]
    def replace(node,path=''):
        if node==source.OLD:occurrences.append(path);return source.NEW
        return node if source.leaf(node)else(replace(node[0],path+'0'),replace(node[1],path+'1'))
    newtree=replace(oldtree);rows=source.sites(newtree);source_raw=source.compact(rows)
    require(len(occurrences)==4 and source_raw==a.sites.read_bytes() and sha(source_raw)==SOURCE_SHA,'Exact four-macro replacement')
    table={key:value for key,value in old.items()if key[0]not in DELETE};table.update(PATCH);table.update(NEW)
    raw=table_bytes(table);require(sha(raw)==TABLE_SHA,'Final native byte identity')
    states={q for q,bit in table};parse_table(raw)
    require(len(states)==219 and len(table)==438,'219 working states, 438 rows required')
    reached={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            z=table[q,bit][2]
            if z!=254 and z not in reached:reached.add(z);todo.append(z)
    require(reached==states,'Graph-unreachable working state')
    # Check every internal source prefix against literal decoder transitions.
    # This is only a decoder relation: all primitive semantics are proved later.
    by_path={};internal=set()
    def walk(node,path=''):
        if source.leaf(node):return
        internal.add(path);by_path[path]=node;walk(node[0],path+'0');walk(node[1],path+'1')
    walk(newtree);allocation={}
    for path in sorted(internal):
        cells={-1:1,**{i:int(b)for i,b in enumerate(path)}};initial=dict(cells);q=84;h=0
        for tick in range(10000):
            if h==len(path):break
            require(h in cells and q!=254,'Decoder touches unrepresented exterior')
            w,d,q=table[q,cells[h]];cells[h]=w;h+=d
        else:raise ValueError('Decoder prefix proof did not terminate')
        require(cells==initial,'Decoder changes source prefix')
        node_sha=sha(source.compact(by_path[path]));allocation.setdefault(q,{}).setdefault(node_sha,[]).append(path)
    roles=sum(len(v)for v in allocation.values());unique={x for v in allocation.values()for x in v}
    require((len(allocation),roles,len(unique),len(states-set(allocation)))==(169,184,183,50),'Decoder/source-role accounting')
    a.output.mkdir(parents=True,exist_ok=True);(a.output/'candidate.tm').write_bytes(raw);(a.output/'sites.json').write_bytes(source_raw)
    dump(a.output/'allocation.json',allocation)
    receipt=dict(status='EXACT_K219_CONSTRUCTION_PASS',working_states=219,transition_rows=438,start=0,dispatcher=84,halt=254,
        table_sha256=TABLE_SHA,source_sha256=SOURCE_SHA,baseline_table_sha256=BASE_TABLE_SHA,baseline_source_sha256=BASE_SOURCE_SHA,
        removed_states=sorted(DELETE),new_states=[301,302],changed_rows=[dict(state=q,read=bit,old=old[q,bit],new=v)for(q,bit),v in sorted(PATCH.items())],
        added_rows=[dict(state=q,read=bit,action=v)for(q,bit),v in sorted(NEW.items())],replaced_source_paths=occurrences,
        source_metrics=source.metrics(newtree),source_internal_nodes=183,decoder_states=169,decoder_roles=184,duplicated_logical_roles=1,
        shared_extra_roles=15,nondecoder_states=50,graph_reachable_states=len(reached),
        scope='Exact syntax, state census and decoder-prefix relation. Mathematical macro equivalence, unbounded primitive semantics and blank startup are separate obligations.')
    dump(a.output/'construction.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
