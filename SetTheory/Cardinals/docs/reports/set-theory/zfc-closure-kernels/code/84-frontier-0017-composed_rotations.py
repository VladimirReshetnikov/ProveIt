#!/usr/bin/env python3
"""Two successive closed-source rotations with inherited origin-aware emission.

This is a discovery screen, not a state-count lower bound.  Every source move
comes from the supplied closed-association/commuting-increment generator.
Only candidates with at most 203 shared source nodes and zero run at most 7
are emitted.  An optional graph-size gate is just a search restriction.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, hashlib, json, os, sys, time

HERE=Path(__file__).resolve().parent
VENDOR=Path(os.environ.get('ZFC_DECODER_VENDOR',str(HERE/'vendor' if (HERE/'vendor').is_dir() else HERE/'archive3/zfc-sub246-research-20261018')))
sys.path.insert(0,str(VENDOR/'search/runtime'))
import source_origin_reuse as O
E,R=O.E,O.R

def mutation(nodes, root, n, expression, old_origins):
    new, seen, origins={}, {}, {}
    def intern(a,b):
        pair=(a,b)
        if pair not in seen:
            seen[pair]=len(new)
            new[seen[pair]]=pair
        return ('N',seen[pair])
    @lru_cache(None)
    def edge(e):
        if e[0]=='N':
            v=edge(expression) if e[1]==n else intern(*(edge(x) for x in nodes[e[1]]))
            origins.setdefault(v[1],set()).update(old_origins.get(e[1],()))
            return v
        if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
        return e
    new_root=edge(('N',root))[1]
    return new,new_root,origins

def digest(nodes,root):
    return hashlib.sha256(json.dumps((root,nodes),sort_keys=True).encode()).hexdigest()

def reachable(U, start='95'):
    seen=set(); todo=[start]
    while todo:
        q=todo.pop()
        if q in seen or q=='254':continue
        seen.add(q)
        for b in (0,1):todo.append(U[q,b][2])
    return seen

def write_table(path,U,states):
    rows=[]
    for (q,b),(w,d,t) in sorted(U.items(),key=lambda x:(int(x[0][0]),x[0][1])):
        if q in states:rows.append(f'{q} {b} {w} {d} {t if t in states or t=="254" else "95"}\n')
    path.write_text('#! start 95\n'+''.join(rows))

def checkpoint(path,payload):
    """Compact atomic output preserves the preceding checkpoint on ENOSPC."""
    temporary=path.with_suffix('.tmp')
    try:
        temporary.write_text(json.dumps(payload,separators=(',',':'))+'\n')
        temporary.replace(path)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise

def compact_records(records):
    out=[]
    for r in records:
        f=r.get('fast')
        if f:
            out.append([r['first'],r['second'],int(r['recycle']),int(r['generic']),f['code'],f['failed_site'],f['failed_branch'],f['error'],f['states']])
        else:out.append(r)
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--all-first',action='store_true')
    ap.add_argument('--graph-max',type=int,default=245)
    ap.add_argument('--verify',action='store_true')
    ap.add_argument('--fast',action='store_true',help='Use C++ sufficient-oracle screen before Python replay.')
    ap.add_argument('--seconds',type=float,default=600)
    a=ap.parse_args()
    out=HERE/(('double_all' if a.all_first else 'double_ties')+('_fast' if a.fast else ''));out.mkdir(exist_ok=True)
    if a.fast:import affine_acceleration as F
    prior=json.loads((VENDOR/'search/runtime/runtime-search-results.json').read_text())
    first=range(len(R.options(O.N))) if a.all_first else prior['origin_emission_rotations_with_246_state_variant']
    options=R.options(O.N); old_origins={n:{n} for n in O.N}
    seen=set(); records=[]; counts=Counter(); best=999; began=time.monotonic(); rank=Counter()
    for i in first:
        n,exp,kind=options[i]
        nodes,root,origins=mutation(O.N,O.root,n,exp,old_origins)
        for j,(m,exp2,kind2) in enumerate(R.options(nodes)):
            counts['ordered_two_move_recipes']+=1
            ns,rt,orig=mutation(nodes,root,m,exp2,origins)
            zm=R.zero_metrics(ns,rt)
            if len(ns)>203 or zm[1]>7 or zm[2]>40:continue
            counts['source_shape_admitted']+=1
            sg=digest(ns,rt)
            if sg in seen:continue
            seen.add(sg); counts['distinct_sources']+=1
            for recycle,generic in ((True,False),(False,False),(True,True),(False,True)):
                U,entry,reused=O.emit(ns,rt,orig,recycle=recycle,generic=generic)
                states=reachable(U); cost=len(states)
                counts['emitted_variants']+=1
                counts[f'graph_cost_{cost}']+=1
                best=min(best,cost)
                if cost>a.graph_max:continue
                rec=dict(first=i,second=j,first_node=n,second_node=m,first_kind=kind,second_kind=kind2,
                         nodes=len(ns),metrics=zm,signature=sg,generic=generic,recycle=recycle,graph_states=cost)
                if a.fast:
                    sites=E.get_sites(ns,rt)
                    fast,used=F.run(U,sites)
                    rec['fast']=fast
                    if fast['code']!=0:
                        counts['fast_'+('rejected' if fast['code']<0 else 'already_246_states')]+=1
                        rec['status']='FAST_REJECTED' if fast['code']<0 else 'AT_LEAST_246_OBSERVED_STATES'
                        records.append(rec)
                        continue
                if a.verify:
                    cases=E.make_cases(E.get_sites(ns,rt)); table=E.Track(U);table.used=set();failure=None
                    for ci in sorted(range(len(cases)),key=lambda k:-rank[k]):
                        pc,branch,target,halt=cases[ci]
                        try:E.A.run(table,pc,branch,target,halt=halt,fuel=2000)
                        except Exception as ex:
                            rank[ci]+=1;failure=dict(case=ci,pc=pc,branch=branch,message=str(ex));break
                    if failure:rec.update(status='affine_rejected',failure=failure);counts['affine_rejected']+=1
                    else:
                        retained={q for q,b in table.used|E.PAIRS}
                        rec.update(status='PASS_GUARDED',retained_states=len(retained));counts['guarded_pass']+=1
                        d=out/f'pass_{i}_{j}_{int(recycle)}{int(generic)}_{len(retained)}';d.mkdir(exist_ok=True)
                        (d/'dag.json').write_text(json.dumps(dict(nodes=ns,root=rt),indent=2)+'\n')
                        (d/'origins.json').write_text(json.dumps({str(k):sorted(v) for k,v in orig.items()},indent=2)+'\n')
                        (d/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
                        write_table(d/'machine.tm',U,retained)
                        print('GUARDED',rec,flush=True)
                else:rec['status']='GRAPH_SCREEN_ONLY'
                records.append(rec)
            if time.monotonic()-began>a.seconds:
                counts['time_limit_hit']=1;break
        checkpoint(out/'results.json',dict(arguments=vars(a),counts=counts,
                   compact_record_fields=['first_recipe','second_recipe','recycle','generic','fast_code','failed_source_leaf','failed_branch','error_code','used_states'],
                   records=compact_records(records),best_graph_states=best,elapsed=time.monotonic()-began))
        print('FIRST',i,'best',best,'counts',dict(counts),'elapsed',round(time.monotonic()-began,2),flush=True)
        if counts['time_limit_hit']:break
    print('COMPLETE',dict(counts),flush=True)

if __name__=='__main__':main()
