#!/usr/bin/env python3
"""Reproducible local timings; includes construction of both dense tables.

Matched finite-ring baseline uses the same denominator cache, precision and
output. Historical baseline is the reviewed exact-rational implementation,
including conversion of its complete output to the same modular ring.
"""
import argparse
import gc
import json
import platform
import statistics
import time
from fast_cauchy import FastCauchy
from verify_kernel import load_historical, need


def timed(fn):
    gc.collect()
    start = time.perf_counter()
    result = fn()
    return time.perf_counter()-start, result


def run(historical=None, repetitions=5):
    records=[]
    hist = load_historical(historical) if historical else None
    for a in (4,5,6,7,8):
        i,t,precision,zeta = max(0,a//3),1<<max(0,a//3),64,(0,1)
        times = {'fast':[], 'matched_cubic':[]}
        stats={}
        for rep in range(repetitions):
            methods = ['fast','matched_cubic'] if rep%2 else ['matched_cubic','fast']
            outputs={}
            for method in methods:
                def work():
                    obj=FastCauchy(a,i,t,precision,zeta)
                    return obj.feature_tables() if method=='fast' else obj.naive_feature_tables()
                duration, result = timed(work)
                times[method].append(duration)
                stats[method]=result.stats
                outputs[method]=result
            need(outputs['fast'].target==outputs['matched_cubic'].target, 'benchmark target mismatch')
            need(outputs['fast'].source==outputs['matched_cubic'].source, 'benchmark source mismatch')
        median={k:statistics.median(v) for k,v in times.items()}
        records.append(dict(dimension=1<<(a-1),a=a,i=i,t=t,precision=precision,zeta=zeta,
                            seconds=times,median_seconds=median,
                            speedup=median['matched_cubic']/median['fast'],stats=stats))
    historical_records=[]
    if hist:
        for a in (3,4,5,6):
            i,t,precision,zeta=0,1,64,(0,1)
            times={'fast':[], 'historical':[]}
            for rep in range(min(repetitions,3)):
                outputs={}
                for method in (['fast','historical'] if rep%2 else ['historical','fast']):
                    def work():
                        if method=='fast':
                            obj=FastCauchy(a,i,t,precision,zeta);tables=obj.feature_tables()
                            return tables.target,tables.source
                        obj=hist.JointCauchyKernel(a,i,t,hist.Quadratic(*zeta))
                        aa,bb=obj.feature_tables()
                        return ([[hist.residue(x,precision) for x in row] for row in aa],
                                [[hist.residue(x,precision) for x in row] for row in bb])
                    duration,result=timed(work)
                    times[method].append(duration);outputs[method]=result
                need(outputs['fast']==outputs['historical'], 'historical benchmark mismatch')
            median={k:statistics.median(v) for k,v in times.items()}
            historical_records.append(dict(dimension=1<<(a-1),a=a,i=i,t=t,precision=precision,zeta=zeta,
                 seconds=times,median_seconds=median,speedup=median['historical']/median['fast']))
    return dict(python=platform.python_version(),platform=platform.platform(),
                processor=platform.processor(),clock='time.perf_counter',repetitions=repetitions,
                matched_modular=records,historical_rational=historical_records,
                scope='Single-machine kernel measurements, not end-to-end SAT benchmarks.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--historical');p.add_argument('--repetitions',type=int,default=5)
    args=p.parse_args();print(json.dumps(run(args.historical,args.repetitions),indent=2))
