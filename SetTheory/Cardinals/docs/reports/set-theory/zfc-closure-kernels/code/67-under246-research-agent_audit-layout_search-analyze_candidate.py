#!/usr/bin/env python3
"""Check closed association equivalence and emit a semantic-ID sparse patch.

This verifier does not trust the MILP solver or the grammar emitter.  It reads
both finite DAGs afresh and computes their full recursively normalized ordered
syntax.  It proves only source equivalence, not correctness of any TM emitter.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent.parent/'sources/beyond252/beyond252/exploratory'

def read(path):
    raw=json.loads(Path(path).read_text())
    return {int(i):tuple(map(tuple,p)) for i,p in raw['nodes'].items()},raw['root']

def normalizer(nodes):
    @lru_cache(None)
    def bound(e):
        if e[0]!='N':
            return (e[1] if e[0]=='B' else int(e[0]=='D'),
                    e[1] if e[0]=='C' else 0)
        x,y=map(bound,nodes[e[1]])
        return max(x[0]-1,y[0]),max(x[1],y[1]-1)
    @lru_cache(None)
    def normal(e):
        if e[0]!='N':return ('L',e)
        a,b=nodes[e[1]];aa,bb=normal(a),normal(b)
        if bound(a)==bound(b)==(0,0):
            aw=aa[1] if aa[0]=='S' else (aa,)
            bw=bb[1] if bb[0]=='S' else (bb,)
            return ('S',aw+bw)
        return ('A',aa,bb)
    return normal,bound

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--source',type=Path,default=SOURCE/'data/original203.json')
    ap.add_argument('--entries',type=Path,default=SOURCE/'historical/decoder_entries.json')
    args=ap.parse_args()
    old,oldroot=read(args.source);new,newroot=read(args.candidate)
    on,ob=normalizer(old);nn,nb=normalizer(new)
    oldnormal=on(('N',oldroot));newnormal=nn(('N',newroot))
    assert oldnormal==newnormal,'Canonical ordered source trees differ'
    oldids={on(('N',i)):i for i in old}
    assert len(oldids)==len(old),'Source has duplicate normalized phrases'
    mapping={};nextid=max(old)+1
    for i in new:
        norm=nn(('N',i))
        if norm in oldids:mapping[i]=oldids[norm]
        else:mapping[i]=nextid;nextid+=1
    assert len(set(mapping.values()))==len(mapping),'Candidate contains duplicate normalized phrases'
    def edge(e):return ('N',mapping[e[1]]) if e[0]=='N' else e
    sparse={mapping[i]:tuple(map(edge,p)) for i,p in new.items()}
    added=sorted(sparse.keys()-old.keys());removed=sorted(old.keys()-sparse.keys())
    changed=[{'node':i,'old':old[i],'new':sparse[i]} for i in sorted(sparse.keys()&old.keys()) if sparse[i]!=old[i]]
    metadata=json.loads(args.entries.read_text())
    states={int(i):int(max(v,key=v.get)) for i,v in metadata['state_entries'].items()}
    retained={states[i] for i in sparse.keys()&old.keys()}
    report=dict(status='PASS',source_nodes=len(old),candidate_nodes=len(new),
        source_file=str(args.source),candidate_file=str(args.candidate),
        source_root=oldroot,candidate_root=newroot,sparse_root=mapping[newroot],
        added_nodes=added,removed_nodes=removed,changed_nodes=changed,
        normalized_root_sha256=hashlib.sha256(json.dumps(oldnormal,separators=(',',':')).encode()).hexdigest(),
        original_modal_entries=len(set(states.values())),retained_modal_entries=len(retained),
        fresh_entries=len(added),semantic_modal_price=len(retained)+len(added),
        orphaned_modal_entries=sorted(set(states.values())-retained),
        claim='The complete ordered syntax agrees after flattening closed sequential nodes. This does not certify a Turing machine.')
    outfile=args.candidate.with_name(args.candidate.stem+'_analysis.json')
    outfile.write_text(json.dumps(report,indent=2)+'\n')
    args.candidate.with_name(args.candidate.stem+'_sparse.json').write_text(json.dumps(dict(root=mapping[newroot],nodes=sparse),indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
