#!/usr/bin/env python3
"""Independent finite comparison of the three frozen incoming U211 tables."""
import json
from common import ROOT,read,census,need,sha,encode,write_json
from independent_source import source_info

def canonical(table,halt):
    mapping={0:0};queue=[0]
    for q in queue:
        for b in(0,1):
            z=table[q,b][2]
            if z!=halt and z not in mapping:mapping[z]=len(mapping);queue.append(z)
    mapping[halt]=len(queue)
    return encode({(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in table.items()})

def check(output):
    old=json.loads((ROOT/'baseline/sites.json').read_text());_,_,oldgraph,_=source_info(old)
    result=[]
    for name,rotations,drop,keep,helper,steps in[
      ('contextual',6,180,163,211,1277525),('research',9,181,220,129,1280108),
      ('rotated',11,218,157,None,1245944)]:
        p=ROOT/'comparison'/name;table=read(p/'u211.native.tm');states=census(table,211)
        dense=read(p/'u211.tm');census(dense,211,211)
        rename={q:i for i,q in enumerate(sorted(states))};rename[254]=211
        need({(rename[q],b):(w,d,rename[z])for(q,b),(w,d,z)in table.items()}==dense,'Dense source mismatch')
        sites=json.loads((p/'sites.json').read_text());_,_,graph,metrics=source_info(sites)
        need(graph==oldgraph,'Incoming proposal changes ordinal source')
        result.append({'name':name,'states':211,'rows':422,'rotations':rotations,'removed_native':drop,
          'representative_native':keep,'helper_native':helper,'metrics':metrics,
          'changed_addresses_from_U212':sum(a[0]!=b[0]for a,b in zip(old,sites)),
          'native_sha256':sha((p/'u211.native.tm').read_bytes()),'dense_sha256':sha((p/'u211.tm').read_bytes()),
          'source_sha256':sha((p/'sites.json').read_bytes()),'canonical_graph_sha256':sha(canonical(table,254)),
          'fresh_symbolic_cases':5084,'fresh_row_coverage':422,'symbolic_inferences':steps})
    need(len({x['canonical_graph_sha256']for x in result})==3,'Inputs are only state renamings')
    r={'status':'THREE_DISTINCT_U211_TABLES_SAME_SOURCE_SEMANTICS','proposals':result,
       'source_primitives':3909,'control_edges':5083,'rooted_transition_graphs_pairwise_nonisomorphic':True,
       'scope':'Literal tables, source semantic equality, and pinned fresh-replay summaries; not three independent theory calibrations.'}
    write_json(output,r);return r
if __name__=='__main__':print(json.dumps(check(ROOT/'build/comparison.json'),indent=2))
