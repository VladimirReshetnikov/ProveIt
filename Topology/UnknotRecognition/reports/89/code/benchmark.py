"""Paired complete interface-query measurements; NOT knot-recognition timings."""
from __future__ import annotations
import json,random,statistics,sys,time,platform
from pathlib import Path
from boundary_sources import CircleSource
from moment_kernel import compile_kernel,compile_kernel_packed
from oracles import block_oracle
from coning_baseline import compile_coning

ROOT=Path(__file__).resolve().parents[1]

def payload(kernel):
    # Common output: first returns, zero/positive distinction, owners and counts.
    # The new method additionally computes exact lengths, which are deliberately
    # excluded from this common-output serialization rather than credited as less work.
    return json.dumps({'pairs':[(a,b,int(l>0)) for a,b,l in kernel.pairs],
        'owners':kernel.port_owners,'active':kernel.active_counts,'passive':kernel.passive_counts},sort_keys=True)

def workload(source,arm):
    packet=source.packet()
    if arm=='coning':kernel,calls=compile_coning(*packet,block_oracle)
    elif arm=='vector':kernel=compile_kernel(*packet,block_oracle);calls=kernel.weighted_calls
    else:kernel=compile_kernel_packed(*packet,block_oracle);calls=kernel.weighted_calls
    return payload(kernel),calls


def run():
    rng=random.Random(6101201)
    configs=[('loop',1,1),('small',8,4),('short',96,16),('ports32',4096,32),
             ('ports64',1000000,64),('binary1024',(1<<1024)+511,16),
             ('binary16384',(1<<16384)+511,16),('few_huge',(1<<16384)+511,2)]
    records=[];summary=[]
    for name,n,p in configs:
        positions=[j*(n//p) for j in range(p)];rng.shuffle(positions)
        src=CircleSource((n,),tuple((0,e) for e in positions),n)
        expected=payload(src.compile(block_oracle));rounds=[]
        for roundno in range(-1,7):
            arms=['packed','vector','coning','packed_control'];rng.shuffle(arms);values={}
            for arm in arms:
                start=time.perf_counter_ns();answer,calls=workload(src,arm);elapsed=time.perf_counter_ns()-start
                if answer!=expected:raise AssertionError('non-equivalent timed outputs')
                values[arm]=elapsed
                records.append({'case':name,'round':roundno,'arm':arm,'nanoseconds':elapsed,'oracle_calls':calls,
                                'output_bytes':len(answer.encode()),'warmup':roundno<0})
            if roundno>=0:rounds.append(values)
        med=lambda arm:statistics.median(r[arm] for r in rounds)/1e6
        ratio=lambda a,b:statistics.median(r[a]/r[b] for r in rounds)
        _,calls=workload(src,'coning')
        summary.append({'case':name,'ports':p,'circle_length_bits':n.bit_length(),'namespace_bits':src.packet()[0].bit_length(),
                        'source_pairings':len(src.packet()[1]),'count_calls':calls,
                        'packed_ms':med('packed'),'vector_ms':med('vector'),'coning_ms':med('coning'),
                        'coning_over_packed':ratio('coning','packed'),
                        'vector_over_packed':ratio('vector','packed'),
                        'packed_control_over_packed':ratio('packed_control','packed')})
    data={'seed':6101201,'python':sys.version,'platform':platform.platform(),'timer':'perf_counter_ns',
          'rounds':7,'warmup_rounds':1,'scope':'Complete circle-interface query using restricted block oracle. Source packet construction, compile, and common-output serialization are timed. No general AHT or knot recognizer benchmark.',
          'summary':summary,'samples':records}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=[r'\begin{tabular}{@{}lrrrrrr@{}}',r'\toprule',r'Case & $p$ & $N$ bits & Calls & Packed ms & Count/packed & A/A \\',r'\midrule']
    for r in summary:
        label=r['case'].replace('_','\\_')
        lines.append(f"{label} & {r['ports']} & {r['namespace_bits']} & {r['count_calls']} & {r['packed_ms']:.3f} & {r['coning_over_packed']:.2f} & {r['packed_control_over_packed']:.2f} \\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (ROOT/'results'/'benchmark_table.tex').write_text('\n'.join(lines)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':run()
