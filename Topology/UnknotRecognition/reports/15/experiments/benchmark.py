"""Paired local-backend benchmarks; not a benchmark of upstream fastunknot.

Input d^2 checks and full certificate construction are outside timed reduction.
All known-valid inputs were generated from complexes by basis changes, or by
crossing attachment. Caches are fresh for each timed run. Five repeats, with
alternating method order. No performance threshold is asserted by tests.
"""
from pathlib import Path
import sys,time,json,statistics,platform,csv
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'tests')]
from radical import *
from fixtures import gauge_complex,sharp_transfer_complex
from braid_scan import scan_braid

def fresh(old):
    a=ArcAlgebra()
    for m in old.pairs[1:]: a.intern(m)
    return a

def main():
    rows=[]; reps=5
    specs=[('gauge-M34-R2',3,16,2,500),('gauge-M66-R2',3,32,2,1300),
           ('gauge-M68-R4',4,32,4,900),('gauge-M100-R4',3,48,4,1800)]
    for label,k,pairs,surv,moves in specs+[('sharp-zigzag-k8',8,0,0,0)]:
        a=ArcAlgebra()
        d=(sharp_transfer_complex(a,k) if not pairs else gauge_complex(a,k,7400+k+pairs,pairs,surv,moves))
        validate_complex(d,a)
        times={m:[] for m in ('profile','transfer','pivot')}; calls={m:[] for m in ('transfer','pivot')}
        expected=survivor_profile(d)
        for rep in range(reps):
            for method in (('profile','transfer','pivot') if rep%2==0 else ('pivot','transfer','profile')):
                aa=fresh(a); start=time.perf_counter()
                if method=='profile': result=survivor_profile(d)
                elif method=='transfer': result=transfer(d,aa,validate=False).d
                else: result=pivot_reduce(d,aa)
                elapsed=time.perf_counter()-start; times[method].append(elapsed)
                if method=='profile': assert result==expected
                else:
                    calls[method].append(aa.nontrivial_calls)
                    assert survivor_profile(result)==expected
                    validate_complex(result,aa)
        row={'name':label,'kind':'fixed-complex','k':k,'M':len(d.src),'R':sum(expected.values()),
             'nnz':d.nnz,'seconds':times,'nontrivial_compositions':calls,
             'median_seconds':{m:statistics.median(v) for m,v in times.items()}}
        row['pivot_over_transfer']=row['median_seconds']['pivot']/row['median_seconds']['transfer']
        rows.append(row); print(label,row['median_seconds'],row['pivot_over_transfer'],flush=True)
    braids=[('torus-2-25',2,[1]*25),('positive-3-12',3,[1,2]*6),
            ('alternating-3-12',3,[1,-2]*6),('braid-relator-unknot',3,[1,2,1,-2,-1,-2]*4+[1,2])]
    for label,k,word in braids:
        times={m:[] for m in ('transfer','pivot')}; reduced_times={m:[] for m in times}; answers={}
        for rep in range(reps):
            for method in (('transfer','pivot') if rep%2==0 else ('pivot','transfer')):
                start=time.perf_counter(); out=scan_braid(k,word,backend=method,validate=False)
                times[method].append(time.perf_counter()-start)
                reduced_times[method].append(sum(x['reduce_seconds'] for x in out['trace']))
                answers[method]=out['unreduced_by_degree']
                maxM=max(x['pre_objects'] for x in out['trace']); maxR=max(x['survivors'] for x in out['trace'])
        assert answers['transfer']==answers['pivot']
        row={'name':label,'kind':'braid-scan','k':k,'word':word,'M':maxM,'R':maxR,
             'by_degree':answers['transfer'],'seconds':times,'reduction_seconds':reduced_times,
             'median_seconds':{m:statistics.median(v) for m,v in times.items()},
             'median_reduction_seconds':{m:statistics.median(v) for m,v in reduced_times.items()}}
        row['pivot_over_transfer']=row['median_seconds']['pivot']/row['median_seconds']['transfer']
        rows.append(row); print(label,row['median_seconds'],row['pivot_over_transfer'],flush=True)
    data={'python':sys.version,'platform':platform.platform(),'repetitions':reps,
          'input_validation_timed':False,'full_certificate_timed':False,'fresh_caches':True,
          'comparison':'local independently implemented minfill pivot baseline, not upstream optimized scanner',
          'rows':rows}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(data,indent=2)+'\n')
    with (ROOT/'results'/'benchmark.csv').open('w',newline='') as f:
        writer=csv.writer(f); writer.writerow(['name','kind','k','M','R','profile_ms','transfer_ms','pivot_ms','pivot_over_transfer'])
        for r in rows:
            med=r['median_seconds']; writer.writerow([r['name'],r['kind'],r['k'],r['M'],r['R'],
                med.get('profile',0)*1000,med['transfer']*1000,med['pivot']*1000,r['pivot_over_transfer']])
if __name__=='__main__': main()
