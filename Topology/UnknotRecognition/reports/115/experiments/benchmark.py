"""Paired complete local queries, plus a deduplicated-set ablation.

The literal and historical algorithms are independently replayed once. The new
solve() already calls its independent replayer before returning, so no redundant
second replay is included in its timed query. Source geometry and I/O are excluded.
"""
from __future__ import annotations
import hashlib,json,platform,random,statistics,sys,time
from math import ceil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'vendor'/'matroidal'))
from dualforest.model import from_dense
from dualforest.solver import solve as old_solve
from dualforest.verify import verify_positive as old_positive,verify_negative as old_negative
from activation_forest import solve
from activation_forest.model import extend_tree
from activation_forest.closure import Activation
from activation_forest.algebra import incidence_vectors
from activation_forest.solve import search_projected,positive_certificate
from .fixtures import parallel_obstruction,repository_loop,choice_arms,generic_positive
from .oracles import brute_solve


def summary(records,left,right):
    a=[x[left]['seconds'] for x in records]; b=[x[right]['seconds'] for x in records]
    return dict(left_median_ms=1000*statistics.median(a),right_median_ms=1000*statistics.median(b),
                median_paired_ratio=statistics.median(x/y for x,y in zip(a,b)))


def main():
    rng=random.Random(55129)
    report=dict(python=sys.version,platform=platform.platform(),seed=55129,
                scope='Validated matrix/graph input to local certificate and one independent replay; no source geometry or whole-knot timing.',
                timing_protocol='Batched timings. Earlier anchored-family controls and noisy initial unbatched data retained separately.',
                choice_family='Unanchored nonlinear loop target; exact-count parity compatible; see fixtures.py.',cases=[],ablation=[])
    fixtures=[('parallel_negative_3',parallel_obstruction(3)),('parallel_negative_5',parallel_obstruction(5)),
              ('parallel_negative_6',parallel_obstruction(6)),('repository_loop',repository_loop()),
              ('choice_arms_2',choice_arms(2)),('choice_arms_5',choice_arms(5)),
              ('generic_positive',generic_positive())]
    for name,inst in fixtures:
        oldinst=from_dense(inst.vertices,inst.edges,inst.matrix)
        def historical():
            ans=old_solve(oldinst,try_incumbent=True)
            ok=old_positive(oldinst,ans['certificate']) if ans['status']=='yes' else old_negative(oldinst,ans['negative_certificate'])
            assert ok
            return dict(status=ans['status'],branches=ans['stats'].get('branches'))
        def proposed():
            ans=solve(inst,seed=7919,try_incumbent=True,max_b=None,max_transitions=None)
            assert ans['status'] in ('SUCCESS','BLOCKED_EXACT')
            return dict(status=ans['status'],route=ans.get('route'),stats=ans['stats'])
        def literal():
            yes,tree,trials=brute_solve(inst)
            if yes: positive_certificate(inst,list(tree))
            # For negative cases, the exhaustive oracle's coverage is the proof:
            # no independent compact negative certificate is claimed for this arm.
            return dict(status='yes' if yes else 'no',tree_trials=trials)
        functions=dict(historical=historical,proposed=proposed,literal=literal)
        batches={}
        for label,fn in functions.items():
            t=time.perf_counter();fn();pilot=time.perf_counter()-t
            batches[label]=min(512,max(1,ceil(.02/max(pilot,1e-9))))
        paired=[]
        for repeat in range(5):
            order=list(functions);rng.shuffle(order);item={'order':order}
            for label in order:
                t=time.perf_counter()
                for _ in range(batches[label]): meta=functions[label]()
                elapsed=time.perf_counter()-t
                item[label]=dict(seconds=elapsed/batches[label],batch=batches[label],batch_seconds=elapsed,**meta)
            paired.append(item)
        aa=[]
        for repeat in range(3):
            values=[]
            for _ in range(2):
                t=time.perf_counter()
                for __ in range(batches['proposed']): proposed()
                values.append((time.perf_counter()-t)/batches['proposed'])
            aa.append(values)
        case=dict(name=name,rows=inst.m,vertices=inst.vertices,boundary=Activation(inst).b,
                  input_sha256=inst.digest(),samples=paired,batches=batches,new_new_control_seconds=aa,
                  historical_over_proposed=summary(paired,'historical','proposed'),
                  literal_over_proposed=summary(paired,'literal','proposed'))
        report['cases'].append(case)
        print(name,case['historical_over_proposed'],case['literal_over_proposed'],flush=True)
    for g in (4,6,8):
        inst=choice_arms(g);vectors=incidence_vectors(inst,2)
        paired=[]
        for repeat in range(5):
            order=['representatives','literal_sets'];rng.shuffle(order);item={'order':order}
            for label in order:
                t=time.perf_counter()
                # Include independent dependency preparation in each arm.
                batch={4:32,6:8,8:2}[g]
                for _ in range(batch):
                    act=Activation(inst)
                    chosen,stats=search_projected(act,vectors,2,reduce_families=label=='representatives')
                    assert chosen is not None
                    positive_certificate(inst,extend_tree(inst,chosen))
                elapsed=time.perf_counter()-t
                item[label]=dict(seconds=elapsed/batch,batch=batch,batch_seconds=elapsed,stats=stats)
            paired.append(item)
        case=dict(arms=g,rows=inst.m,boundary=Activation(inst).b,input_sha256=inst.digest(),samples=paired,
                  literal_sets_over_representatives=summary(paired,'literal_sets','representatives'))
        report['ablation'].append(case)
        print('ablation',g,case['literal_sets_over_representatives'],flush=True)
    report['source_hashes']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                             for folder in ('activation_forest','vendor/matroidal/dualforest','experiments')
                             for p in sorted((ROOT/folder).glob('*.py'))}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
