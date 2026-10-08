"""Paired presentation-query timings and compressed capacity/parameter tests.

No upstream recognizer or PD pipeline is timed. These cases are not offered as
a hard-knot corpus. Construction is excluded; fresh validation, solving and
certificate replay are included in paired query timings.
"""
import json,platform,random,statistics,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from su2budget.slp import Arena,Presentation,from_words
from su2budget import dihedral as D,univariate as U
from su2budget.degrees import profile
from su2budget.fixtures import huge_braid_relation


def query(data,arm):
    p=Presentation.from_dict(data)
    backend=U if arm=='univariate' else D
    result=backend.solve(p)
    assert result['status']!='UNKNOWN'
    assert backend.verify(p,result)
    return result


def mixed_presentation(m):
    a=Arena();xs=[a.letter(i+1) for i in range(m)]
    power=xs[0];cuts=[]
    for _ in range(m):power=a.concat(power,power);cuts.append(power)
    word=a.word([g for i in range(1,m+1) for j in range(1,m+1) for g in (i,j)])
    p=a.presentation(m,[(a.concat(power,word),0)],label='synthetic checkpoint tradeoff; not a knot claim')
    return p,cuts


def main():
    rng=random.Random(918);paired=[]
    for pvalue in (3,5,9,17,33,65):
        m=(pvalue-1)//2
        p=from_words(2,[([1,2]*m+[1],[2]+[1,2]*m)],meridians=True,
                     label=f'T(2,{pvalue}) meridional presentation')
        data=p.to_dict()
        for arm in ('dihedral','control','univariate'):query(data,arm)
        timings={a:[] for a in ('dihedral','control','univariate')}
        sample=None
        for _ in range(5):
            arms=list(timings);rng.shuffle(arms)
            for arm in arms:
                start=time.perf_counter()
                for repeat in range(20):result=query(data,arm)
                timings[arm].append((time.perf_counter()-start)/20)
                if arm=='univariate':sample=result
        medians={a:statistics.median(v) for a,v in timings.items()}
        paired.append(dict(p=pvalue,rank=p.rank,live_nodes=len(p.live()),
                           raw_seconds=timings,median_seconds=medians,
                           ratio_univariate_over_dihedral=medians['univariate']/medians['dihedral'],
                           positive_root_count=sample['roots']['count'],
                           univariate_degree=sample['peak_degree'],
                           univariate_coefficient_bits=sample['peak_coefficient_bits']))
    capacity=[]
    for bits in (64,256,1024,4096,10000):
        p=huge_braid_relation(bits)
        times=[]
        for _ in range(3):
            start=time.perf_counter();result=D.solve(p);assert D.verify(p,result)
            times.append(time.perf_counter()-start)
        assert result['gcd']==2**(bits+1)+1
        capacity.append(dict(squaring_depth=bits,live_nodes=len(p.live()),
                             represented_torus_parameter=f'2^{bits+1}+1',
                             peak_exponent_bits=result['peak_exponent_bits'],
                             raw_seconds=times,median_seconds=statistics.median(times),
                             status=result['status']))
    tradeoff=[]
    for m in (4,8,16,32,64):
        p,cuts=mixed_presentation(m)
        a,b,c=profile(p),profile(p,p.products()),profile(p,cuts)
        tradeoff.append(dict(m=m,live_products=len(p.products()),
                             no_checkpoints=dict(count=0,delta_bits=a.delta.bit_length(),kappa=a.kappa),
                             all_checkpoints=dict(count=len(b.checkpoints),delta=b.delta,kappa=b.kappa),
                             mixed_checkpoints=dict(count=len(c.checkpoints),delta=c.delta,kappa=c.kappa)))
    out=dict(platform=platform.platform(),python=platform.python_version(),
             processor=platform.processor(),clock='time.perf_counter',seed=918,
             paired_scope='fresh Presentation validation + solve + certificate replay; construction excluded',
             paired_trials=5,queries_per_paired_batch=20,capacity_trials=3,paired=paired,capacity=capacity,tradeoff=tradeoff,
             limitation='No whole-recognizer timings or production integration test suite was run.')
    path=Path(__file__).resolve().parents[1]/'data'/'benchmarks.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    for row in paired:print(row['p'],row['median_seconds'],row['ratio_univariate_over_dihedral'])
    for row in capacity:print('capacity',row)
    for row in tradeoff:print('tradeoff',row)

if __name__=='__main__':main()
