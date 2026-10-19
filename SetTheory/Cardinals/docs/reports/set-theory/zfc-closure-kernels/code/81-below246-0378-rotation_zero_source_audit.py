#!/usr/bin/env python3
"""Independently check the zero-run-six source graph against Prog254.v.

The graph is untrusted input. It is expanded into a literal binary tree,
then checked using the independent Boolean-list arithmetic and direct
tree decoder from rotation245_source_audit.py. No searcher is imported.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import rotation245_source_audit as a

def expand(data):
    entries={int(k):tuple(v) for k,v in data['entries'].items()}
    seen=set();active=set();nodes=[]
    def visit(i):
        assert i in entries and i not in active
        seen.add(i);active.add(i)
        e=entries[i];op=e[0]
        if op=='N':
            assert len(e)==3
            n=len(nodes);nodes.append(None)
            left=visit(e[1]);right=visit(e[2]);nodes[n]=(left,right)
            result=('CN',n)
        else:
            assert len(e)==2 and op in ('CI','CD','CB','CC','CH')
            if op in ('CI','CD'):assert isinstance(e[1],int) and 0<=e[1]<9
            elif op in ('CB','CC'):assert isinstance(e[1],int) and 1<=e[1]<=3
            else:assert e[1] is None
            result=e
        active.remove(i);return result
    assert visit(data['root'])==('CN',0)
    assert seen==set(entries)
    return nodes

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    parser.add_argument('--source',type=Path,default=here.parent/'sources/context246/zfc-context246/sources/Prog254.v')
    parser.add_argument('--graph',type=Path,default=here/'rotation_zero_candidate_24.json')
    parser.add_argument('--output-dir',type=Path,default=here)
    args=parser.parse_args();raw=args.source.read_bytes();graph=args.graph.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==a.SOURCE_SHA
    old=a.parse(raw);new=expand(json.loads(graph))
    oldleaves,_=a.leaves_of(old);newleaves,_=a.leaves_of(new)
    assert len(old)==len(new)==6459
    assert [(op,n) for p,op,n in oldleaves]==[(op,n) for p,op,n in newleaves]
    old_lookup={p:i for i,(p,_,_) in enumerate(oldleaves)}
    new_lookup={p:i for i,(p,_,_) in enumerate(newleaves)}
    records=[]
    for i,((p,op,n),(q,_,_)) in enumerate(zip(oldleaves,newleaves)):
        for positive in ([False,True] if op=='CD' else [None]):
            left=a.decoder(old,old_lookup,a.source_successor(p,op,n,positive))
            right=a.decoder(new,new_lookup,a.source_successor(q,op,n,positive))
            assert left==right,(i,p,q,op,n,positive,left,right)
            records.append([i,positive,left])
    assert len(records)==8391
    assert a.decoder(old,old_lookup,'')==a.decoder(new,new_lookup,'')==0
    oldgroups,_=a.unique_subtrees(old);newgroups,_=a.unique_subtrees(new)
    histogram=Counter(max(map(len,p.split('1'))) for p,_,_ in newleaves)
    assert len(oldgroups)==203 and len(newgroups)==202 and max(histogram)==6
    out=dict(status='PASS exact source equivalence; binary machine uncompiled',
        source_sha256=a.SOURCE_SHA,graph_sha256=hashlib.sha256(graph).hexdigest(),
        literal_nodes=6459,instruction_leaves=6460,guards_compared=8391,
        original_unique_pairs=203,new_unique_pairs=202,maximum_zero_run=6,
        maximum_depth=max(len(p) for p,_,_ in newleaves),zero_histogram=dict(histogram),
        all_register_effects_identical=True,all_control_operands_identical=True,
        all_successor_leaf_indices_identical=True,initial_leaf_identical=True,
        no_unreachable_case_exemption=True,
        leaf_map=[[p,q,op,n] for (p,op,n),(q,_,_) in zip(oldleaves,newleaves)],
        guarded_successors=records)
    args.output_dir.mkdir(exist_ok=True,parents=True)
    (args.output_dir/'rotation_zero_source_certificate.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    (args.output_dir/'rotation_zero_program_tree.json').write_text(json.dumps(dict(nodes=new,root=0),separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('leaf_map','guarded_successors')},indent=2))

if __name__=='__main__':main()
