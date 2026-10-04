"""Paired cold-process comparisons. Timeouts are censored, NOT measured runtimes.
Run: python tools/benchmark.py --repeats 3 --cap 20
Default run takes a few minutes because of censored baseline cases.
"""
import argparse,json,platform,statistics,subprocess,sys
from datetime import datetime,timezone
from common import ROOT,load,power_sum

def run(backend,mode,path,cap):
    cmd=[sys.executable,str(ROOT/'tools'/'benchmark_worker.py'),backend,mode,str(path),'--cap',str(cap)]
    try: done=subprocess.run(cmd,text=True,capture_output=True,timeout=cap+4)
    except subprocess.TimeoutExpired:
        return {'backend':backend,'mode':mode,'status':'HARD_TIMEOUT','seconds':None,
                'hard_process_limit_seconds':cap+4}
    if done.returncode:raise RuntimeError(f'worker failed: {cmd}\n{done.stderr}\n{done.stdout}')
    return json.loads(done.stdout)

def main():
    p=argparse.ArgumentParser();p.add_argument('--repeats',type=int,default=3)
    p.add_argument('--cap',type=float,default=20);p.add_argument('--output',default='results/benchmark.json')
    args=p.parse_args()
    if args.repeats<1 or args.cap<=0:p.error('positive repeats and cap required')
    for k in (2,3,12):
        d=power_sum(load('conway.json'),k)
        (ROOT/'examples'/f'conway_sum_{k}.json').write_text(json.dumps(d.to_json(),indent=2))
    from fastunknot import Diagram
    for n in (64,256,1024):
        d=Diagram.from_braid(n+1,range(1,n+1))
        (ROOT/'examples'/f'unknot_chain_{n}.json').write_text(json.dumps(d.to_json()))
    cases=[]
    for filename in ('conway.json','kinoshita_terasaka.json','hard_unknot_8.json',
                     'random5_36.json','unknot_braid40.json','torus_3_5.json'):
        for mode in ('scan','pipeline'):cases.append((filename,mode,('baseline','optimized')))
    for k in (2,3):
        cases.append((f'conway_sum_{k}.json','forced-scan-pipeline',('baseline','optimized')))
    for n in (64,256,1024):cases.append((f'unknot_chain_{n}.json','order',('baseline','optimized')))
    cases += [('random5_36.json','scan',('cached-lifo','old-algebra-fill')),
              ('conway_sum_12.json','factored',('optimized',))]
    report={'python':sys.version,'platform':platform.platform(),'processor':platform.processor(),
            'timestamp_utc':datetime.now(timezone.utc).isoformat(),'soft_cap_seconds':args.cap,
            'repeats_requested':args.repeats,'import_and_parse_timed':False,
            'cold_process_each_sample':True,'measurements':[]}
    output=ROOT/args.output
    for filename,mode,backends in cases:
        for backend in backends:
            samples=[]
            for _ in range(args.repeats):
                sample=run(backend,mode,ROOT/'examples'/filename,args.cap);samples.append(sample)
                if sample['status']!='OK':break
            times=[x['seconds'] for x in samples if x['status']=='OK']
            row={'case':filename,'mode':mode,'backend':backend,'samples':samples,
                 'median_seconds':statistics.median(times) if len(times)==len(samples) else None}
            report['measurements'].append(row);output.parent.mkdir(parents=True,exist_ok=True)
            output.write_text(json.dumps(report,indent=2))
            print(filename,mode,backend,row['median_seconds'] or samples[-1]['status'],flush=True)
    target=[x for x in report['measurements'] if x['case']=='random5_36.json' and x['mode']=='scan']
    ranks=[s['answer']['reduced_rank'] for row in target for s in row['samples'] if s['status']=='OK']
    if not ranks or len(set(ranks))!=1:raise ArithmeticError(f'inconsistent difficult-case ranks: {ranks}')
    report['hard_case_successful_ranks_agree']=True;report['hard_case_reduced_rank']=ranks[0]
    output.write_text(json.dumps(report,indent=2))

if __name__=='__main__':main()
