#!/usr/bin/env python3
"""Paired, shuffled, same-machine kernel measurements (not production timings)."""
from pathlib import Path
import sys,json,random,statistics,time,platform,os
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from shear_kernel.slp import Grammar
from shear_kernel.optimize import optimize,verify_optimization
from shear_kernel.reference import selected_line_step
from shear_kernel.presentation import pure_power_terminal
from shear_kernel.histogram import reference_profile,reduced_image

ROOT=Path(__file__).resolve().parents[1]

def star(k,h):
    g=Grammar(); roots=[]
    for j in range(k):
        node=g.concat(g.letter(j+2),g.run(1,(j+1)*2**h))
        w=2**(h+2*(k-j))
        roots.extend([g.power(node,w),g.power(node,w+1)])
    return g,roots,list(range(1,k+2))

def line_checked(g,roots,alive):
    out,new,info=selected_line_step(g,roots,alive)
    if info['gain']:
        p=reference_profile(g,roots,info['multiplier'])
        if sum(out.meta[x].length for x in new)!=p.value(info['potentials']):
            raise AssertionError('line output length')
    return out,new,info

def step(g,roots,alive,arm):
    if arm=='selected_line':
        out,new,info=line_checked(g,roots,alive)
        return {'length':sum(out.meta[x].length for x in new),'rules':len(out.reachable(new))}
    forced=arm=='shear_flow'
    o=optimize(g,roots,alive,balanced_fast_path=not forced,forest_fast_path=not forced)
    verify_optimization(g,roots,o.certificate)
    return {'length':o.certificate['optimal_length'],'rules':len(o.grammar.reachable(o.roots)),
            'methods':[r['method'] for r in o.certificate['solutions']],
            'flow_phases':sum(r['phases'] for r in o.certificate['solutions'])}

def descent(g,roots,alive,arm):
    count=0
    while pure_power_terminal(g,roots,alive) is None:
        if count>64: raise AssertionError('unexpected long synthetic descent')
        before=sum(g.meta[x].length for x in roots)
        if arm=='selected_line': g,roots,info=line_checked(g,roots,alive)
        else:
            forced=arm=='shear_flow'
            o=optimize(g,roots,alive,balanced_fast_path=not forced,forest_fast_path=not forced)
            verify_optimization(g,roots,o.certificate); g,roots=o.grammar,o.roots
        count+=1
        if sum(g.meta[x].length for x in roots)>=before: raise AssertionError('synthetic descent stalled')
    t=pure_power_terminal(g,roots,alive)
    if not t['is_infinite_cyclic']: raise AssertionError('wrong terminal classification')
    return {'length':sum(g.meta[x].length for x in roots),'phases':count,
            'rules':len(g.reachable(roots)),'is_infinite_cyclic':True}

def measure_case(name,g,roots,alive,query,rng,reps,arms):
    for arm in arms: query(g,roots,alive,arm)  # one excluded warm-up per arm
    samples=[]
    for rep in range(reps):
        order=list(arms); rng.shuffle(order)
        for slot,arm in enumerate(order):
            t=time.perf_counter_ns(); result=query(g,roots,alive,arm); elapsed=time.perf_counter_ns()-t
            samples.append({'round':rep,'slot':slot,'arm':arm,'ns':elapsed,'result':result})
    medians={arm:statistics.median(x['ns'] for x in samples if x['arm']==arm)/1e6 for arm in arms}
    outputs={arm:next(x['result'] for x in samples if x['arm']==arm) for arm in arms}
    if 'shear_flow' in arms and outputs['shear_flow']['length']!=outputs['shear_structured']['length']:
        raise AssertionError('same-query shear engines disagree')
    return {'name':name,'initial_length':sum(g.meta[x].length for x in roots),
            'input_rules':len(g.reachable(roots)),'medians_ms':medians,'outputs':outputs,'samples':samples}

def main():
    rng=random.Random(2026100807); corpus=json.loads((ROOT/'results/braid_corpus.json').read_text())
    records=[]; arms=['selected_line','shear_structured','shear_flow']
    for i,item in enumerate(corpus):
        for stage in (0,1):
            words=item['original_relators'] if stage==0 else item['post_elimination_relators']
            alive=list(range(1,item['strands']+1)) if stage==0 else item['alive']
            g=Grammar(); roots=[g.word(w) for w in words]
            records.append(measure_case(f'braid-{i:03d}-{stage}',g,roots,alive,step,rng,5,arms))
    synthetic=[]
    for k,h in ((3,20),(6,20),(12,20),(3,100),(6,100),(3,500),(6,500)):
        g,roots,alive=star(k,h)
        synthetic.append(measure_case(f'star-Z-k{k}-h{h}',g,roots,alive,descent,rng,5,arms))
    totals={arm:sum(r['medians_ms'][arm] for r in records) for arm in arms}
    summary={'python':platform.python_version(),'platform':platform.platform(),'processor':platform.processor(),
             'cpu_count':os.cpu_count(),'seed':2026100807,'repetitions':5,
             'braid_stages':len(records),'measured_braid_calls':len(records)*5*3,
             'measured_synthetic_calls':len(synthetic)*5*3,'braid_sum_medians_ms':totals,
             'scope':'preconstructed algebraic stages, independent witness checks included; not upstream pipeline',
             'synthetic_scope':'full shear/selected-line descent to the same pure-power infinite-cyclic terminal'}
    (ROOT/'results/benchmark.json').write_text(json.dumps({'summary':summary,'braid_stages':records,'synthetic':synthetic},indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    for r in synthetic: print(r['name'],r['medians_ms'],{a:v.get('phases') for a,v in r['outputs'].items()})
if __name__=='__main__': main()
