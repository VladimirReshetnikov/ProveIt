"""Reproducible paired microbenchmarks. Raw samples are retained, no timeouts
are counted as speedups, and no claim about the maintained recognizer is made.
"""
import json, csv, sys, platform, time, statistics, random
from pathlib import Path
from christoffel import *
from checker import verify_power
from oracle import whitehead_primitive_power
from braid_bridge import produce, validate_braid
from contraction import balanced_family, run_contractions

OUT=Path(__file__).resolve().parents[1]/'data'
RNG=random.Random(20261008)


def timed(f):
    t=time.perf_counter();result=f();return time.perf_counter()-t,result


def compact_case(steps, h):
    A,r=fibonacci_slp(steps);r=A.power(r,2**h+1)
    ans=classify(A.rules,r)
    assert ans.certificate and verify_power(A.rules,ans.certificate)
    return A,r


def literal_case(steps,h):
    A,r=fibonacci_slp(steps);r=A.power(r,2**h+1)
    word=A.expand(r,cap=2_000_000)
    ok,d=whitehead_primitive_power(word)
    assert ok and d==2**h+1
    return A,r


def main():
    report={'environment':{'python':sys.version,'platform':platform.platform(),
                            'timer':'time.perf_counter','seed':20261008},
            'paired_kernel':[], 'large_kernel':[], 'paired_braid_bridge':[],
            'parallel_contraction':[]}
    for steps,h in [(8,0),(12,0),(16,0),(10,4),(10,8),(10,12)]:
        samples={'compressed':[],'literal_whitehead':[]}
        compact_case(steps,h);literal_case(steps,h)
        for _ in range(5):
            arms=list(samples);RNG.shuffle(arms)
            for arm in arms:
                sec,(A,r)=timed(lambda: (compact_case if arm=='compressed' else literal_case)(steps,h))
                samples[arm].append(sec)
        med={arm:statistics.median(v) for arm,v in samples.items()}
        report['paired_kernel'].append(dict(steps=steps,power_bits=(2**h+1).bit_length(),
            nodes=len(A.rules),expanded_length=A.lengths[r],samples_seconds=samples,
            median_seconds=med,ratio_literal_over_compressed=med['literal_whitehead']/med['compressed']))
    for steps,h in [(64,64),(256,256),(1024,1024),(4096,4096)]:
        samples=[]
        for _ in range(5):
            sec,(A,r)=timed(lambda:compact_case(steps,h));samples.append(sec)
        report['large_kernel'].append(dict(steps=steps,power_bits=(2**h+1).bit_length(),nodes=len(A.rules),
            expanded_length_bits=A.lengths[r].bit_length(),samples_seconds=samples,
            median_seconds=statistics.median(samples),literal_status='NOT_RUN_EXPANSION_EXCEEDS_CAP'))
    # Fixed source braids, independently replayed in each arm.
    corpus=[]
    rng=random.Random(801104)
    for strands in (2,3,4):
        for k in range(12):
            base=list(range(1,strands))
            sleeve=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(k%4)]
            word=sleeve+base+[-x for x in sleeve[::-1]]
            corpus.append((strands,word,'unknot_by_conjugation_of_stabilized_circle'))
    for strands in (2,3,4):
        for k in (3,5,7,9):
            word=[1]*k+list(range(2,strands))
            corpus.append((strands,word,'nontrivial_torus_knot_with_stabilization'))
    for idx,(b,w,label) in enumerate(corpus):
        samples={'width':[],'whitehead':[]};status={}
        for _ in range(5):
            arms=list(samples);RNG.shuffle(arms)
            for arm in arms:
                sec,result=timed(lambda:produce(b,w,engine=arm))
                samples[arm].append(sec);status[arm]=result['status']
        assert status['width']==status['whitehead']
        assert status['width']!='UNKNOT' or label.startswith('unknot')
        report['paired_braid_bridge'].append(dict(id=idx,strands=b,word=w,label=label,
            status=status,samples_seconds=samples,
            median_seconds={arm:statistics.median(x) for arm,x in samples.items()}))
    for depth in (2,4,6,8):
        A,roots,alive=balanced_family(depth,32)
        seconds,result=timed(lambda:run_contractions(A.rules,roots,alive))
        assert len(result['alive'])==1
        report['parallel_contraction'].append(dict(depth=depth,initial_rank=len(alive),
            initial_nodes=len(A.rules),seconds=seconds,rounds=result['rounds'],
            final_nodes=len(result['rules']),final_rank=len(result['alive'])))
    bridge=report['paired_braid_bridge']
    width_total=sum(x['median_seconds']['width'] for x in bridge)
    wh_total=sum(x['median_seconds']['whitehead'] for x in bridge)
    report['bridge_summary']=dict(cases=len(bridge),certified_unknots=sum(x['status']['width']=='UNKNOT' for x in bridge),
        width_sum_of_case_medians=width_total,whitehead_sum_of_case_medians=wh_total,
        ratio_whitehead_over_width=wh_total/width_total,
        note='Isolated capped literal braid bridge, NOT production fastunknot benchmark')
    (OUT/'benchmark_results.json').write_text(json.dumps(report,indent=2)+'\n')
    with (OUT/'kernel_summary.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['fibonacci_steps','power_bits','nodes','expanded_length','compressed_seconds','literal_seconds','ratio'])
        for x in report['paired_kernel']:
            w.writerow([x['steps'],x['power_bits'],x['nodes'],x['expanded_length'],x['median_seconds']['compressed'],x['median_seconds']['literal_whitehead'],x['ratio_literal_over_compressed']])
    print(json.dumps({'kernel':[(x['nodes'],x['expanded_length'],round(x['ratio_literal_over_compressed'],2)) for x in report['paired_kernel']],
                      'large':[(x['nodes'],x['expanded_length_bits'],x['median_seconds']) for x in report['large_kernel']],
                      'bridge':report['bridge_summary']},indent=2))

if __name__=='__main__':main()
