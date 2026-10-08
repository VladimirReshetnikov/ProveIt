#!/usr/bin/env python3
"""Paired kernel benchmarks. No end-to-end upstream recognizer claim."""
from __future__ import annotations
import json,platform,random,statistics,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from portkh import gf2
from portkh.complexes import analyze,connected_singular_pair
from portkh.explicit import from_dense
from cube_oracle import cube,square_zero


def timed(fn,repeats):
    start=time.perf_counter_ns()
    value=None
    for _ in range(repeats):value=fn()
    return (time.perf_counter_ns()-start)*1e-9/repeats,value


def paired(baseline,treatment,rng,batch,rounds=7):
    data=[]
    for j in range(rounds):
        funcs={'base':baseline,'port':treatment,'control':baseline}
        order=list(funcs);rng.shuffle(order)
        row={'order':order}
        values=[]
        for name in order:
            elapsed,value=timed(funcs[name],batch);row[name]=elapsed;values.append(value)
        assert values[0]==values[1]==values[2]
        data.append(row)
    return {'batch':batch,'trials':data,
            'baseline_median_seconds':statistics.median(x['base'] for x in data),
            'port_median_seconds':statistics.median(x['port'] for x in data),
            'paired_speedup_median':statistics.median(x['base']/x['port'] for x in data),
            'aa_ratio_median':statistics.median(x['base']/x['control'] for x in data)}


def explicit_connected(m):
    size=1 << m
    # Favorable explicit competitor: construct only the nonzero two-term block,
    # not a full 2*size square differential, then use bit-packed elimination.
    rows=[(1 << j)^7 for j in range(size)]
    return 2*size-2*gf2.rank(rows)


def main():
    if not __debug__:
        raise RuntimeError('Audit assertions require Python without -O')
    rng=random.Random(61008);examples=[];knots=[]
    for m in (4,6,8,10,12,14):
        c=connected_singular_pair(m)
        analyze(c);explicit_connected(m)
        ans=paired(lambda m=m:explicit_connected(m),lambda c=c:analyze(c)['homology_dimension'],
                   rng,5 if m<=10 else 1)
        ans.update({'register_length':m,'virtual_dimension':c.dimension,'width':4,'ports':1,
                    'family':'connected abstract two-term example; not a knot benchmark'})
        examples.append(ans)
    huge=[]
    for m in (40,200,1000):
        c=connected_singular_pair(m)
        trials=[timed(lambda:analyze(c),1) for _ in range(7)]
        result=trials[0][1]
        huge.append({'register_length':m,'virtual_dimension':c.dimension,
             'median_seconds':statistics.median(t for t,_ in trials),
             'all_seconds':[t for t,_ in trials], 'width':4,'ports':1,
             'beta':result['homology_dimension'],'core_shape':result['core_shape'],
             'candidate_rows':result['register_summaries'][0]['candidate_rows'],
             'explicit_baseline_executed':False})
    for name,s,w in [('unknot_stabilized',3,[1,2]),('trefoil',2,[1,1,1]),
                      ('figure_eight',3,[1,-2,1,-2]),('unknot_relator',3,[1,2,2,-2])]:
        rows,degrees=cube(s,w)
        def baseline():
            assert square_zero(rows)
            return len(rows)-2*gf2.rank(rows)
        def treatment():return analyze(from_dense(rows,degrees))['homology_dimension']
        ans=paired(baseline,treatment,rng,5)
        ans.update({'name':name,'strands':s,'word':w,'dimension':len(rows),
                    'ports':from_dense(rows,degrees).ports,'beta':baseline()})
        knots.append(ans)
    result={'format':'portkh-benchmark-1','python':sys.version,'platform':platform.platform(),
       'clock':'perf_counter_ns','seed':61008,'rounds':7,'abstract_examples':examples,
       'compressed_only':huge,'small_knot_cube_bridge':knots,
       'scope':'Algebra-kernel timings only. No upstream pipeline or recognition speedup measured.',
       'timed_work':{'abstract_baseline':'construct nonzero block from closed formula and exact rank',
                    'abstract_treatment':'analyze prepared register, including degree and square-zero checks',
                    'cube_baseline':'square-zero check and direct rank of prepared cube',
                    'cube_treatment':'explicit-to-port producer and symbolic analyzer of prepared cube'},
       'excluded':'imports, parsing, disk I/O; cube construction excluded from both cube arms'}
    (ROOT/'data'/'benchmarks.json').write_text(json.dumps(result,indent=2)+'\n')
    for x in examples:print('abstract',x['register_length'],x['paired_speedup_median'],x['aa_ratio_median'])
    for x in huge:print('huge',x['register_length'],x['median_seconds'])
    for x in knots:print('cube',x['name'],x['paired_speedup_median'])

if __name__=='__main__':main()
