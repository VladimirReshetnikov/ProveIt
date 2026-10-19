#!/usr/bin/env python3
"""Independently replay every saved C++ decision with the original Python engine.

Failure is failure of a sufficient symbolic rule system, not proof that a
mutated TM lacks the requested semantics. A state-cover witness concerns the
uniform instruction-contract/pruning discipline, not blank-run reachability.
"""
from pathlib import Path
from itertools import groupby
from collections import Counter
import argparse,json,time
import composed_rotations as D
import affine_acceleration as F
E,R,O=D.E,D.R,D.O
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--ledger',type=Path,default=HERE/'double_all_fast/results.json');ap.add_argument('--output',type=Path,default=HERE/'independent-record-replay.json');a=ap.parse_args()
    assert __debug__
    data=json.loads(a.ledger.read_text());records=data['records']
    assert len(records)==data['counts']['emitted_variants']
    assert len({tuple(r[:4]) for r in records})==len(records)
    options=R.options(O.N);initial_origins={n:{n} for n in O.N};priority=json.loads((HERE/'case_order.json').read_text())['priority_leaf_indices']
    counts=Counter();examples=[];started=time.monotonic();last_first=None
    for (first,second),group in groupby(records,key=lambda r:tuple(r[:2])):
        if first!=last_first:
            n,exp,kind=options[first]
            first_nodes,first_root,first_origins=D.mutation(O.N,O.root,n,exp,initial_origins)
            second_options=R.options(first_nodes);last_first=first
        m,exp2,kind2=second_options[second]
        ns,rt,origins=D.mutation(first_nodes,first_root,m,exp2,first_origins)
        zm=R.zero_metrics(ns,rt);assert len(ns)<=203 and zm[1]<=7 and zm[2]<=40
        sites=E.get_sites(ns,rt);assert len(sites)==6460
        order=priority+[i for i in range(len(sites)) if i not in set(priority)]
        local_cases={}
        checked_tables={}
        def cases(i):
            if i not in local_cases:local_cases[i]=E.make_cases([sites[i]])
            return local_cases[i]
        for rec in group:
            _,_,recycle,generic,code,failed,branch,error,fast_states=rec
            U,entries,reused=O.emit(ns,rt,origins,recycle=bool(recycle),generic=bool(generic))
            assert all(U[p]==E.T[p] for p in E.PAIRS)
            counts['replayed_variants']+=1
            table_identity=tuple(sorted(U.items()))
            if table_identity in checked_tables:
                assert checked_tables[table_identity]==code
                counts['byte_identical_table_cache_hits']+=1
                counts['confirmed_sufficient_checker_rejections' if code==-1 else 'confirmed_at_least246_label_covers']+=1
                continue
            if code==-1:
                selected=(sites[failed][2],branch==1) if sites[failed][1]=='CD' else None
                pc,b,target,halt=next(c for c in cases(failed) if c[1]==selected)
                try:E.A.run(U,pc,b,target,halt=halt,fuel=2000)
                except Exception as ex:
                    counts['confirmed_sufficient_checker_rejections']+=1
                    counts['symbolic_fuel_rejections' if str(ex)=='symbolic fuel exhausted' else 'other_sufficient_checker_rejections']+=1
                    if len(examples)<8:examples.append(dict(recipe=rec[:4],site=failed,branch=branch,cpp_error=error,python_error=str(ex)))
                else:raise AssertionError(('C++ false rejection',rec))
            elif code==1:
                fast,_=F.run(U,sites)
                assert fast['code']==1,('changed C++ screen result',rec,fast)
                table=E.Track(U);table.used=set(E.PAIRS);replayed=0
                for i in fast['witness_leaf_indices']:
                    for pc,b,target,halt in cases(i):E.A.run(table,pc,b,target,halt=halt,fuel=2000)
                    replayed+=1
                    if len({q for q,b in table.used})>=246:break
                else:raise AssertionError(('C++ false state cover',rec))
                counts['confirmed_at_least246_label_covers']+=1
                counts['source_leaves_replayed_for_covers']+=replayed
                counts['maximum_leaves_in_one_cover']=max(counts['maximum_leaves_in_one_cover'],replayed)
            else:raise AssertionError(('Unexpected sub246 survivor needs full verification',rec))
            checked_tables[table_identity]=code
        if counts['replayed_variants']%500<4:print('REPLAY',dict(counts),flush=True)
    assert counts['confirmed_sufficient_checker_rejections']==data['counts']['fast_rejected']
    assert counts['confirmed_at_least246_label_covers']==data['counts']['fast_already_246_states']
    out=dict(status='PASS_INDEPENDENT_PYTHON_REPLAY',counts=counts,examples=examples,elapsed=time.monotonic()-started,
             scope='Every reported decision is replayed by the inherited Python sufficient oracle. Coverage enumeration remains a separate reproducible driver. No global state lower bound or blank-run claim.')
    D.checkpoint(a.output,out);print(json.dumps(out,indent=2))
if __name__=='__main__':main()
