#!/usr/bin/env python3
"""Independent all-register source audit of the final colored candidate."""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import rotation245_source_audit as a
from rotation_zero_source_audit import expand

def main():
    here=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=here.parent/'sources/context246/zfc-context246/sources/Prog254.v')
    parser.add_argument('--graph',type=Path,default=here.parent/'agent_states/colored_context_candidate_003.json')
    parser.add_argument('--output',type=Path,default=here/'colored_context_source_certificate.json')
    args=parser.parse_args();raw=args.source.read_bytes();graph=args.graph.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==a.SOURCE_SHA
    old=a.parse(raw);new=expand(json.loads(graph))
    ol,_=a.leaves_of(old);nl,_=a.leaves_of(new)
    assert len(ol)==len(nl)==6460
    assert [(op,n) for p,op,n in ol]==[(op,n) for p,op,n in nl]
    oi={p:i for i,(p,_,_) in enumerate(ol)};ni={p:i for i,(p,_,_) in enumerate(nl)}
    rows=[]
    for i,((p,op,n),(q,_,_)) in enumerate(zip(ol,nl)):
        for positive in ([False,True] if op=='CD' else [None]):
            x=a.decoder(old,oi,a.source_successor(p,op,n,positive))
            y=a.decoder(new,ni,a.source_successor(q,op,n,positive))
            assert x==y,(i,p,q,op,n,positive,x,y)
            rows.append([i,positive,x])
    assert len(rows)==8391
    assert a.decoder(old,oi,'')==a.decoder(new,ni,'')==0
    oc,_=a.unique_subtrees(old);nc,_=a.unique_subtrees(new)
    histogram=Counter(len(p)-len(p.rstrip('0')) for p,op,n in nl if op=='CD')
    out=dict(status='PASS exact all-register source equivalence',
        graph=args.graph.name,graph_sha256=hashlib.sha256(graph).hexdigest(),
        original_source_sha256=a.SOURCE_SHA,original_pairs=len(oc),new_pairs=len(nc),
        leaves=len(nl),guarded_cases=len(rows),maximum_depth=max(len(p) for p,_,_ in nl),
        maximum_zero_run=max(max(map(len,p.split('1'))) for p,_,_ in nl),
        CDtrailingzero_histogram=dict(histogram),all_operations_and_operands_identical=True,
        all_guarded_targets_identical=True,
        leaf_map=[[p,q,op,n] for (p,op,n),(q,_,_) in zip(ol,nl)],guarded_successors=rows,
        binary_proof_boundary='This independent audit verifies source only; separate literal table/frame/boot certificates are required.')
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('leaf_map','guarded_successors')},indent=2))

if __name__=='__main__':main()
