"""Paired matrix-stage comparisons. Not full unknot-recognition benchmarks."""
import itertools
import json
import platform
import random
import statistics
import time
from pathlib import Path
from dualforest import from_dense, solve, solve_pair, verify_positive, verify_pair_optimality
from dualforest.solver import positive_certificate
from .oracles import literal_peel, tree_oracle


def star_family(q, easy=False, blocked=False):
    edges = [(0, i+1) for i in range(q) for _ in range(2)]
    rows = [[0]*q for _ in edges]
    for i in range(q):
        rows[2*i + int(easy)][i] = 1
    if blocked:
        edges.append((0,0))
        rows.append([0]*q)
    return from_dense(q+1, edges, rows)


def pair_query(inst):
    ans = solve_pair(inst)
    if ans['status'] == 'yes':
        assert verify_positive(inst, ans['certificate'])
    else:
        assert verify_pair_optimality(inst, ans['optimality'])
    return ans['status'] == 'yes'


def star_enumeration(inst, q):
    # This generator lists only actual spanning trees of this multigraph;
    # it does not charge enumeration of non-tree edge subsets.
    for bits in itertools.product((0,1), repeat=q):
        tree = [2*i+b for i,b in enumerate(bits)]
        if literal_peel(inst, tree) is not None:
            cert = positive_certificate(inst, tree)
            assert verify_positive(inst, cert)
            return True
    return False


def loop_fpt(inst):
    ans = solve(inst, try_incumbent=False)
    assert ans['status'] == 'yes' and verify_positive(inst, ans['certificate'])
    return True


def loop_enum(inst):
    ans = tree_oracle(inst)
    assert ans['yes']
    assert verify_positive(inst, positive_certificate(inst, ans['tree']))
    return True


def paired(name, a, b, rounds, rng, expected):
    for fn in (a,b):
        assert fn() == expected  # untimed warmup
    samples = []
    for _ in range(rounds):
        order = ['selector','enumeration']
        rng.shuffle(order)
        values = {}
        for label in order:
            start = time.perf_counter_ns()
            got = (a if label=='selector' else b)()
            values[label] = (time.perf_counter_ns()-start)*1e-9
            assert got == expected
        samples.append(dict(order=order, **values))
    controls=[]
    for _ in range(3):
        values=[]
        for copy in range(2):
            start=time.perf_counter_ns(); assert a()==expected
            values.append((time.perf_counter_ns()-start)*1e-9)
        controls.append(values)
    return dict(name=name, samples=samples, identical_selector_controls=controls,
                selector_median_s=statistics.median(s['selector'] for s in samples),
                enumeration_median_s=statistics.median(s['enumeration'] for s in samples),
                median_paired_ratio=statistics.median(s['enumeration']/s['selector'] for s in samples),
                aa_median_ratio=statistics.median(x[1]/x[0] for x in controls))


def run():
    rng=random.Random(9122026)
    rows=[]
    for q in (1,4,8,12):
        for kind in ('unique_late','easy_first','obstructed'):
            inst=star_family(q,easy=kind=='easy_first',blocked=kind=='obstructed')
            name=f'{kind}_q{q}'
            record=paired(name,lambda:pair_query(inst),lambda:star_enumeration(inst,q),5,rng,kind!='obstructed')
            record.update(q=q, trees=2**q, rows=inst.m, nonzeros=sum(map(len,inst.rows)),
                          trees_inspected=1 if kind=='easy_first' else 2**q)
            rows.append(record)
            print(name,record['selector_median_s'],record['enumeration_median_s'],record['median_paired_ratio'],flush=True)
    inst=from_dense(2,[(0,1)]*4+[(1,1)],[[0,0,1,0,0],[1,1,0,0,0],[0,1,0,1,1],
                                             [1,0,1,1,1],[0,1,1,1,0]])
    rows.append(paired('repository_loop_matrix',lambda:loop_fpt(inst),lambda:loop_enum(inst),7,rng,True))
    result=dict(python=platform.python_version(),platform=platform.platform(),seed=9122026,
                stage='Already parsed matrix/graph -> local exact decision; positive replay included. Pair negatives also replay optimality.',
                excluded='Native geometric source construction, source authentication, whole-cut and complete unknot recognition.',
                family_caveat='Synthetic rooted-star matrices; no manifold-realization claim.',records=rows)
    (Path(__file__).resolve().parents[1]/'results'/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({r['name']:r['median_paired_ratio'] for r in rows},indent=2))

if __name__=='__main__':
    run()
