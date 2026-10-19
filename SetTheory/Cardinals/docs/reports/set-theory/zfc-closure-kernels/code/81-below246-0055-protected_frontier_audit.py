#!/usr/bin/env python3
"""Independent source/retained-context audit of the protected frontier.

No search code is imported. The ordinary trace-equivalence proof follows
from the checked finite successor and register-update identities. Retained
source contexts are evidence for a binary compiler, not its correctness
certificate: terminal handlers borrow additional rows.
"""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib
import json
import argparse
import rotation245_source_audit as a
from rotation_zero_source_audit import expand

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'sources/context246/zfc-context246'

def intervals(nodes):
    result={};cursor=0
    def visit(n):
        nonlocal cursor
        start=cursor
        for op,k in nodes[n]:
            if op=='CN':visit(k)
            else:cursor+=1
        result[n]=(start,cursor)
    visit(0)
    assert len(set(result.values()))==len(nodes)
    return result

def structural_classes(old,new):
    intern={}
    def ident(e):
        if e not in intern:intern[e]=len(intern)
        return intern[e]
    def classes(nodes):
        result={}
        def edge(op,k):return visit(k) if op=='CN' else ident((op,k))
        def visit(n):
            result[n]=ident(('pair',*(edge(*e) for e in nodes[n])))
            return result[n]
        visit(0);return result
    return classes(old),classes(new)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec',type=Path,default=HERE/'protected_frontier_spec.json')
    parser.add_argument('--source',type=Path,default=BASE/'sources/Prog254.v')
    parser.add_argument('--table',type=Path,default=BASE/'machine/zfc_prefix246_old.tm')
    parser.add_argument('--graph',type=Path)
    parser.add_argument('--output-dir',type=Path,default=HERE)
    args=parser.parse_args();spec=json.loads(args.spec.read_text())
    graph_path=args.graph or args.spec.parent/spec['graph']
    raw=args.source.read_bytes();graph=graph_path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==a.SOURCE_SHA==spec['source_sha256']
    assert hashlib.sha256(graph).hexdigest()==spec['graph_sha256']
    old=a.parse(raw);new=expand(json.loads(graph))
    ol,op=a.leaves_of(old);nl,np=a.leaves_of(new)
    assert len(ol)==len(nl)==6460
    assert [(o,n) for p,o,n in ol]==[(o,n) for p,o,n in nl]
    oi={p:i for i,(p,_,_) in enumerate(ol)};ni={p:i for i,(p,_,_) in enumerate(nl)}
    guards=[]
    for i,((p,opx,n),(q,_,_)) in enumerate(zip(ol,nl)):
        for positive in ([False,True] if opx=='CD' else [None]):
            target=a.decoder(old,oi,a.source_successor(p,opx,n,positive))
            assert target==a.decoder(new,ni,a.source_successor(q,opx,n,positive))
            guards.append([i,positive,target])
    assert len(guards)==8391
    assert a.decoder(old,oi,'')==a.decoder(new,ni,'')==0
    oc,nc=structural_classes(old,new)
    assert len(set(oc.values()))==len(set(nc.values()))==203
    protected={oc[n] for n in spec['protected_source_representatives']}
    assert len(protected)==93 and protected.issubset(nc.values())

    # Recompute every original decoder-node entry state from the literal
    # table, rather than trusting the optimization search's state map.
    table_raw=args.table.read_bytes()
    assert hashlib.sha256(table_raw).hexdigest()==spec['table_sha256']
    table={}
    for line in table_raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b)
        assert key not in table;table[key]=(int(w),1 if d=='R' else -1,int(t))
    original_state={};state_classes=defaultdict(set)
    for n,p in op.items():
        tape={i:int(bit) for i,bit in enumerate(p)};head=0;q=96
        for tick in range(10000):
            if head==len(p):break
            bit=tape.get(head,0);write,move,q=table[q,bit]
            tape[head]=write;head+=move
        else:raise AssertionError(('node entry fuel',n,p))
        assert all(tape.get(i,0)==int(b) for i,b in enumerate(p))
        original_state[n]=q;state_classes[q].add(oc[n])
    shared={q for q,cs in state_classes.items() if len(cs)>1}
    assert len(shared)==12
    osp=intervals(old);nsp=intervals(new);new_node_at={span:n for n,span in nsp.items()}
    context_records=[]
    for n,q in original_state.items():
        if q not in shared:continue
        span=osp[n];assert span in new_node_at
        m=new_node_at[span];depth=spec['alias_context_depths'][str(q)]
        assert oc[n]==nc[m] and op[n][-depth:]==np[m][-depth:]
        context_records.append([n,m,q,depth,op[n][-depth:]])
    assert len(context_records)==518
    tail_hist=Counter(len(p)-len(p.rstrip('0')) for p,opx,n in nl if opx=='CD')
    remaining=[]
    for i,((p,opx,n),(q,_,_)) in enumerate(zip(ol,nl)):
        if opx=='CD' and len(q)-len(q.rstrip('0'))>=7:
            remaining.append(dict(leaf_index=i,logical_register=n,old_path=p,new_path=q,
                old_guard_cases=[c for c,g in enumerate(guards) if g[0]==i]))
    assert len(remaining)==5 and max(tail_hist)==7
    out=dict(status='PASS source theorem; five short-scanner obstructions remain',
        source_sha256=a.SOURCE_SHA,graph_sha256=spec['graph_sha256'],
        original_pairs=203,new_pairs=203,leaves=6460,guarded_cases=8391,
        maximum_zero_run=max(max(map(len,p.split('1'))) for p,_,_ in nl),
        maximum_depth=max(len(p) for p,_,_ in nl),
        all_operations_and_arguments_identical=True,all_guarded_successors_identical=True,
        preserved_subtree_classes=93,preserved_shared_state_classes=12,
        preserved_incoming_context_occurrences=518,trailing_decrement_zero_histogram=dict(tail_hist),
        remaining_short_scanner_obstructions=remaining,
        binary_status='Not certified: terminal-handler borrowed rows need a compiler proof and literal validation.',
        leaf_map=[[p,q,opx,n] for (p,opx,n),(q,_,_) in zip(ol,nl)],
        guarded_successors=guards,retained_contexts=context_records)
    args.output_dir.mkdir(exist_ok=True,parents=True)
    (args.output_dir/'protected_frontier_certificate.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    concise={k:v for k,v in out.items() if k not in ('leaf_map','guarded_successors','retained_contexts')}
    (args.output_dir/'protected_frontier_summary.json').write_text(json.dumps(concise,indent=2)+'\n')
    print(json.dumps(concise,indent=2))

if __name__=='__main__':main()
