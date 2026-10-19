#!/usr/bin/env python3
"""Occurrence-specific deletion of two product-proved empty transfer loops.

Research driver. Its source graph certificate is conditional on the checked
product invariant. The independent identity-collapse checker is a separate gate.
"""
from pathlib import Path
import argparse,json,sys,time
from collections import Counter
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[2]
OUTPUT=PACKAGE/'verification/fusion/zero_specialization'
sys.path[:0]=[str(PACKAGE/'code/grammar'),str(PACKAGE/'code/proof')]
import search246 as s
import rotate_search as r
from plateau_search import reach,minimize
from control_rotations import intern_sites
from leaf_cfg import Program,increment,strip,digest
CERT=PACKAGE/'reference/guard-invariant/product-invariant.json'
PREFIXES={'X':'1110100101100011','T':'1111110'}
BASE_SITES=s.sites(s.NODES,s.ROOT)
SRC=Program(BASE_SITES)
INDEX={pc:i for i,(pc,op,arg) in enumerate(BASE_SITES)}
MASKS=json.loads(CERT.read_text())['masks']

def metrics(nodes,root):
    table,_=s.emit(nodes,root);states=reach(table)
    return len(states),minimize(table,states)

def feasible(pc,guard):
    masks=MASKS[INDEX[pc]]
    if masks is None:return False
    op,arg=SRC.by_address[pc]
    if op!='CD':return True
    return bool(masks[arg] & (1 if guard=='zero' else 6))

def normalize(pc,deleted):
    seen=set()
    while pc in deleted:
        assert pc not in seen;seen.add(pc)
        op,arg=SRC.by_address[pc]
        masks=MASKS[INDEX[pc]]
        assert masks is not None and op=='CD' and masks[arg]==1,(pc,op,arg,masks)
        pc=SRC.successors(pc)['zero']
    return pc

def repair(sites,mapping,deleted):
    dst=Program(sites);fixed=[];edits=[];edges=0
    inverse={v:k for k,v in mapping.items()}
    for pc,op,arg in sites:
        old=inverse[pc]
        expected={g:mapping[normalize(t,deleted)] for g,t in SRC.successors(old).items() if feasible(old,g)}
        if op not in ('CB','CC'):
            actual=dst.successors(pc)
            if any(actual[g]!=t for g,t in expected.items()):return None,dict(reason='arithmetic_successor',pc=pc,old=old,expected=expected,actual=actual)
            fixed.append((pc,op,arg));edges+=len(expected);continue
        if not expected or dst.successors(pc)==expected:
            fixed.append((pc,op,arg));edges+=len(expected);continue
        target=expected['always'];choices=[]
        for edge,bit in s.CONTROL_OPTIONS:
            if bit!=int(pc[-1]):continue
            typ,k=edge
            after=increment(strip(pc,'0',k)) if typ=='B' else strip(pc,'1',k)
            if dst.decode(after)==target:choices.append((typ!=op[1:],k,typ))
        if not choices:return None,dict(reason='no_control_encoding',pc=pc,old=old,expected=expected)
        _,k,typ=min(choices)
        fixed.append((pc,'C'+typ,k));edits.append([pc,op,arg,'C'+typ,k]);edges+=1
    dst=Program(fixed)
    for old,pc in mapping.items():
        assert SRC.signature(old)==dst.signature(pc)
        for g,t in SRC.successors(old).items():
            if feasible(old,g):assert dst.successors(pc)[g]==mapping[normalize(t,deleted)]
    assert mapping[normalize(SRC.initial,deleted)]==dst.initial
    certificate=dict(status='PASS',feasible_edges=edges,source_leaves=len(BASE_SITES),target_leaves=len(fixed),deleted_indices=sorted(INDEX[p] for p in deleted),mapped_indices=[INDEX[inverse[p]] for p,_,_ in fixed],source_sites_sha256=digest(BASE_SITES),target_sites_sha256=digest(fixed),mapping_sha256=digest(mapping),control_edits=edits,scope='Product-invariant-conditioned one-step identity collapse; no binary machine or bootstrap claim.')
    return (fixed,certificate),None

def collapse(keys):
    prefixes=[PREFIXES[k] for k in keys];sites=[];mapping={};deleted=set()
    for pc,op,arg in BASE_SITES:
        newpc=pc
        for prefix in prefixes:
            if pc.startswith(prefix+'0'):deleted.add(pc);break
            if pc.startswith(prefix+'1'):newpc=prefix+pc[len(prefix)+1:]
        else:
            sites.append((newpc,op,arg));mapping[pc]=newpc
    repaired,failure=repair(sites,mapping,deleted)
    if failure:return None,failure
    ss,cert=repaired;nn,nr=intern_sites(ss)
    return (nn,nr,ss,cert,mapping,deleted),None

def emit_record(name,nn,nr,sites,certificate,extra):
    T,entries=s.emit(nn,nr)
    graph,charged=metrics(nn,nr)
    reachable=reach(T)
    data=dict(name=name,root=nr,nodes=nn,sites=sites,source_certificate=certificate,graph_states=graph,charged_states=charged,zero_metrics=r.zero_metrics(nn,nr),**extra)
    (OUTPUT/f'{name}.json').write_text(json.dumps(data,indent=2)+'\n')
    (OUTPUT/f'{name}.sites.json').write_text(json.dumps(sites)+'\n')
    (OUTPUT/f'{name}.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(T.items(),key=lambda z:(int(z[0][0]),z[0][1])) if q in reachable))
    return data

def main():
    global OUTPUT
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--base-only',action='store_true',help='Emit only X, T, and XT, without the 718 closed proposals.')
    args=ap.parse_args()
    if not __debug__:raise RuntimeError('Run without -O.')
    OUTPUT=args.output.resolve();OUTPUT.mkdir(parents=True,exist_ok=True)
    from audit_guard_transport import parse_source,cases,check_product
    independently_parsed=parse_source(PACKAGE/'reference/context246/sources/Prog254.v')
    assert independently_parsed.sites==BASE_SITES
    check_product(json.loads(CERT.read_text()),cases(independently_parsed))
    results=[];began=time.monotonic()
    for keys in ['X','T','XT']:
        candidate,failure=collapse(keys)
        if failure:print(keys,failure,flush=True);results.append(dict(keys=keys,failure=failure));continue
        nn,nr,ss,cert,mapping,deleted=candidate
        base=emit_record('collapse'+keys,nn,nr,ss,cert,{})
        print(keys,'base',base['graph_states'],base['charged_states'],len(nn),flush=True)
        records=[];hist=Counter();best=base['charged_states']
        for i,(n,e,k) in enumerate([] if args.base_only else r.options(nn)):
            nodes,root=r.mutate(nn,nr,n,e)
            new=s.sites(nodes,root)
            ordermap=dict(zip(sorted(p for p,_,_ in ss),sorted(p for p,_,_ in new)))
            newmap={old:ordermap[pc] for old,pc in mapping.items()}
            repaired,fail=repair(new,newmap,deleted)
            if fail:hist['source_fail']+=1;continue
            new,certificate=repaired;nodes,root=intern_sites(new)
            try:g,c=metrics(nodes,root)
            except (KeyError,IndexError):hist['unsupported']+=1;continue
            hist[str(c)]+=1;records.append(dict(index=i,node=n,kind=k,graph_states=g,charged_states=c))
            if c<best or c<246:
                best=min(best,c)
                emit_record(f'collapse{keys}-rotation{i}',nodes,root,new,certificate,dict(rotation_index=i,rotation_kind=k))
                print(keys,'rotation',i,k,g,c,flush=True)
        results.append(dict(keys=keys,base_graph=base['graph_states'],base_charged=base['charged_states'],decoder_nodes=len(nn),single_closed_moves=0 if args.base_only else len(r.options(nn)),best_charged=best,histogram=hist,records=records))
    summary=dict(results=results,seconds=time.monotonic()-began)
    (OUTPUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in q.items() if k!='records'} for q in results],indent=2),flush=True)
if __name__=='__main__':main()
