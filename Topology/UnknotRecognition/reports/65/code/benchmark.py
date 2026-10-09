"""Paired SAME-GENERATOR complete abstract assembly measurements.

Both modes deduplicate exact partitions. Only the representative reduction
switch differs. Solver timings include validation, deduplication, reduction,
and witness tracking; shared grammar construction and literal replay are out
of the timed region. This is not a whole-knot or native fastunknot benchmark.
"""
from __future__ import annotations
import argparse,json,platform,random,statistics,sys,time
from pathlib import Path
from disk_kernel import Candidate,canonical,partitions
from assembly import Layer,solve,replay_surface


def instance(r, stages=2):
    rng=random.Random(20261009+r)
    initial=tuple(Candidate(p,rng.randrange(-100,1000)) for p in partitions(r))
    options=[Candidate(tuple(range(r))*2,0)]
    for i in range(r):
        for j in range(i+1,r):
            p=canonical(i if x==j else x for x in list(range(r))*2)
            options.append(Candidate(p,1+rng.randrange(20)))
    layer=Layer(r,r,tuple(options))
    cap=canonical(i//2 for i in range(r))
    return initial,[layer]*stages,[Candidate(cap,0)]


def run(widths,repeats):
    data=[]
    for r in widths:
        initial,layers,caps=instance(r)
        timings={'exact':[],'representative':[]};last={}
        for trial in range(repeats):
            for mode in (['exact','representative'] if trial%2==0 else ['representative','exact']):
                t=time.perf_counter();out=solve(initial,layers,caps,compressed=mode=='representative')
                timings[mode].append(time.perf_counter()-t);last[mode]=out
        a,b=last['exact'],last['representative']
        assert (a['status'],a['cost'])==(b['status'],b['cost'])
        replay=replay_surface(initial,layers,caps,b['witness'])
        assert replay['is_disk'] and replay['cost']==b['cost']
        ta,tb=map(statistics.median,(timings['exact'],timings['representative']))
        row={'width':r,'initial_candidates':len(initial),'layers':len(layers),'options_per_layer':len(layers[0].options),
             'times_seconds':timings,'median_exact':ta,'median_representative':tb,'ratio_exact_over_representative':ta/tb,
             'exact_stats':a['stats'],'representative_stats':b['stats'],'optimum':b['cost'],
             'witness_replay':replay}
        data.append(row);print(r,round(ta,5),round(tb,5),round(ta/tb,2),flush=True)
    # A no-reuse control: reduction should not be claimed free.
    initial,_,caps=instance(8)
    control={}
    for mode in ('exact','representative'):
        t=time.perf_counter();answer=solve(initial,[],caps,compressed=mode=='representative')
        control[mode+'_seconds']=time.perf_counter()-t
        control[mode+'_cost']=answer['cost']
    assert control['exact_cost']==control['representative_cost']
    return {'python':sys.version,'platform':platform.platform(),'repeats':repeats,
            'scope':'complete explicit abstract assembly grammar, not unknot recognition',
            'measurements':data,'no_reuse_control':control}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--widths',type=int,nargs='+',default=[6,7,8]);ap.add_argument('--repeats',type=int,default=3)
    ap.add_argument('--output',default='results/benchmark.json');a=ap.parse_args()
    data=run(a.widths,a.repeats);Path(a.output).write_text(json.dumps(data,indent=2)+'\n')
