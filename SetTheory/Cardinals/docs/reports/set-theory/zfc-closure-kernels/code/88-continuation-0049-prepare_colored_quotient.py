#!/usr/bin/env python3
"""Transport exact leaf-control classes and generate finite colored-TM fixtures.

The source-CFG equality is checked exactly. The literal executions produced
here are finite discovery tests, never a universal candidate certificate.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
import importlib.util,sys,json,argparse,time,hashlib
ROOT=Path(__file__).resolve().parents[2]
R=output_directory()
sys.path.insert(0,str(ROOT/'vendor/context246/code'))
import check_literal_instructions as lit
P=Path(__file__).with_name('source_decoder.py')
spec=importlib.util.spec_from_file_location('independent_source_decoder',P)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def derive_quotient(graph):
    """Greatest guarded bisimulation after terminating CB/CC erasure.

    A failure to reach an arithmetic/halting leaf is rejected rather than
    equated to a terminating chain. Class identifiers use first occurrence
    order, so the result is deterministic.
    """
    n=len(graph);epsilon=[None]*n;rank=[None]*n;active=set()
    def erase(i):
        if epsilon[i] is not None:return epsilon[i],rank[i]
        assert i not in active,'Pure control cycle cannot be silently erased'
        active.add(i);op,successors=graph[i]
        if op[0] in ('B','C'):
            assert len(successors)==1
            endpoint,steps=erase(successors[0]);epsilon[i]=endpoint;rank[i]=steps+1
        else:
            assert op[0] in ('I','D','H')
            epsilon[i]=i;rank[i]=0
        active.remove(i);return epsilon[i],rank[i]
    for i in range(n):erase(i)
    def number(keys):
        known={};result=[]
        for key in keys:
            if key not in known:known[key]=len(known)
            result.append(known[key])
        return result
    classes=number(tuple(graph[epsilon[i]][0]) for i in range(n));rounds=0
    while True:
        new=number((tuple(graph[epsilon[i]][0]),
                    tuple(classes[j] for j in graph[epsilon[i]][1]))
                   for i in range(n))
        rounds+=1
        if new==classes:break
        classes=new
    # Finite fixed-point certificate: each class has one observable label
    # and one ordered list of successor classes after control erasure.
    signatures={}
    for i,c in enumerate(classes):
        j=epsilon[i];signature=(tuple(graph[j][0]),tuple(classes[k] for k in graph[j][1]))
        assert signatures.setdefault(c,signature)==signature
        if rank[i]:
            successor=graph[i][1][0]
            assert rank[successor]==rank[i]-1 and classes[successor]==c
    return {'graph':graph,'classes':classes,'rank':rank,'epsilon':epsilon,
            'rounds':rounds,'count':len(set(classes)),
            'scope':'Exact guarded quotient of this parsed candidate source after terminating control-only erasure; no source-equivalence or TM-runtime theorem is inferred.'}

def same_partition(a,b):
    left={};right={}
    return len(a)==len(b) and all(left.setdefault(x,y)==y and right.setdefault(y,x)==x for x,y in zip(a,b))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('--span',type=int,default=64)
    ap.add_argument('--derive-quotient',action='store_true',help='Recompute the exact quotient from the candidate CFG instead of transporting unchanged leaf order')
    args=ap.parse_args();assert __debug__
    begun=time.monotonic();stem=Path(args.stem)
    gp=stem.with_suffix('.json');tp=stem.with_suffix('.tm')
    obj=json.loads(gp.read_text());entries={int(i):e for i,e in obj['entries'].items()}
    nodes={s:tuple(('N',c) if entries[c][0]=='N' else ((entries[c][0][1],entries[c][1]) if entries[c][0]!='CH' else ('H',)) for c in e[1:]) for s,e in entries.items() if e[0]=='N'}
    dec=m.Decoder(nodes,obj['root'])
    reference=json.loads((ROOT/'experiments/audit_inputs/quotient.json').read_text())
    graph=json.loads(json.dumps(dec.graph()));unchanged=graph==reference['graph']
    if args.derive_quotient:
        control=derive_quotient(reference['graph'])
        assert same_partition(control['classes'],reference['classes'])
        assert control['rank']==reference['rank']
        cert=derive_quotient(graph)
    else:
        assert unchanged,'Changed CFG requires --derive-quotient'
        cert=reference
    classes=cert['classes'];rank=cert['rank']
    assert len(classes)==len(dec.sites)==6460
    # Unfold the source DAG because the matcher must distinguish leaf
    # occurrences having different continuations, even under shared nodes.
    unfolded=[];leaves=[]
    def unfold(edge,path):
        if edge[0]!='N':
            i=len(leaves);leaves.append((path,edge));return -i-1
        i=len(unfolded);unfolded.append(None)
        unfolded[i]=[unfold(child,path+str(b))for b,child in enumerate(nodes[edge[1]])]
        return i
    root=unfold(('N',dec.root),'');assert leaves==dec.sites and len(unfolded)==6459
    target=R/stem.name;target.mkdir(exist_ok=True)
    if args.derive_quotient:(target/'derived_quotient.json').write_text(json.dumps(cert,indent=2)+'\n')
    with (target/'decoder.txt').open('w') as out:
        print(len(unfolded),root,len(leaves),file=out)
        for row in unfolded:print(*row,file=out)
        for c,r in zip(classes,rank):print(c,r,file=out)
    T=lit.read_table(tp);cases=0;ticks=0;maxsteps=0;case_map=[]
    with (target/'quotient_cases.txt').open('w') as out:
        for pc,e in dec.sites:
            op='C'+e[0];r=e[1] if len(e)>1 else None
            for positive in ((False,True)if op=='CD' else (None,)):
                regs=[i*3%7 for i in range(9)]
                if op=='CD':regs[lit.PHYSICAL[r]]=1 if positive else 0
                spares=[0];head=0;span=args.span
                want=lit.expected(pc,op,r,regs,spares,head,span)
                initial=lit.paint(pc,span,regs,spares,head)
                steps,used,visits=lit.run_case(T,pc,op,r,regs,spares,head,span,fuel=5000)
                ticks+=steps;cases+=1;maxsteps=max(maxsteps,steps)
                if want is None:expected_class=0;max_rank=0;halt=254;h=0;nxt='';rv=regs;sv=spares
                else:
                    h,_,nxt,_,rv,sv=want;leaf=dec.leaf(nxt)
                    expected_class=classes[leaf];max_rank=rank[leaf];halt=96
                items=[expected_class,max_rank,len(initial),*sorted(initial),halt,h,nxt or '-',*rv,len(sv),*sv,len(used),*sorted(2*q+b for q,b in used)]
                print(*items,file=out)
                case_map.append({'case':cases-1,'path':pc,'operation':op,'logical_register':r,
                                 'positive':positive,'next_path':nxt,'expected_class':expected_class,
                                 'maximum_rank':max_rank})
    assert cases==8391
    (target/'case_map.json').write_text(json.dumps(case_map,indent=2)+'\n')
    result={'status':'PASS','output_directory':str(R),'source_guarded_graph_unchanged':unchanged,'quotient_derived_from_candidate':args.derive_quotient,
            'quotient_class_count':len(set(classes)),'maximum_noop_rank':max(rank),'finite_cases':cases,'literal_steps':ticks,'maximum_case_steps':maxsteps,'span':args.span,'elapsed_seconds':time.monotonic()-begun,'scope':'Exact source-control quotient construction/transport and finite literal fixture generation; no changed-TM universal proof.',
            'input_hashes':{str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in (gp,tp,ROOT/'experiments/audit_inputs/quotient.json')}}
    (target/'preparation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
