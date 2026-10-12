"""Follow up the noisy Fibonacci paired regression after full validation jobs finish."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources


def baseline():
    modules={}
    for name in ('core_handlebody','bundle_boundary_kernel','normal_cut_handlebodies'):
        key='fastunknot._deferred_baseline_'+name
        spec=importlib.util.spec_from_file_location(key,DATA/'deferred-forest-baseline'/(name+'.py'))
        m=importlib.util.module_from_spec(spec);sys.modules[key]=m;spec.loader.exec_module(m);modules[name]=m
    modules['bundle_boundary_kernel']._chosen_forest=modules['core_handlebody']._chosen_forest
    modules['normal_cut_handlebodies'].core_handlebody_certificate=modules['core_handlebody'].core_handlebody_certificate
    modules['normal_cut_handlebodies'].bundle_boundary_kernel=modules['bundle_boundary_kernel'].bundle_boundary_kernel
    return modules['normal_cut_handlebodies'].normal_cut_handlebodies


def main():
    pins=sources();old=baseline()
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    ids=['fibonacci_lst_09/mixed']
    report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                baseline_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (DATA/'deferred-forest-baseline').glob('*.py')},
                corpus_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                python=sys.version,platform=platform.platform(),seed=261012112,cases=[])
    rng=random.Random(report['seed'])
    def query(c,method):
        start=time.perf_counter()
        r=(old if method=='before' else normal_cut_handlebodies)(c['triangulation'],c['coordinates'],record_certificate=True)
        produced=time.perf_counter()
        if r['status']=='COMPLETE':assert verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],r['certificate'])
        end=time.perf_counter()
        return r,dict(produce=produced-start,replay=end-produced,total=end-start)
    for key in ids:
        c=next(c for c in bank if c['id']==key)
        a,_=query(c,'before');b,_=query(c,'after')
        shared=a['status']==b['status']=='COMPLETE'
        if shared:assert a['census']==b['census']
        samples=[];aa=[]
        for _ in range(5):
            order=['before','after'];rng.shuffle(order);s=dict(order=order)
            for mode in order:
                r,t=query(c,mode);assert r['status']==(a if mode=='before' else b)['status'];s[mode]=t
            samples.append(s)
        for _ in range(3):
            _,a1=query(c,'before');_,a2=query(c,'before');aa.append(dict(first=a1['total'],second=a2['total'],ratio=a1['total']/a2['total']))
        record=dict(id=key,before_status=a['status'],after_status=b['status'],comparable_successes=shared,
                    before_median=statistics.median(s['before']['total'] for s in samples),
                    after_median=statistics.median(s['after']['total'] for s in samples),
                    paired_speedup=statistics.median(s['before']['total']/s['after']['total'] for s in samples) if shared else None,
                    aa_median=statistics.median(s['ratio'] for s in aa),samples=samples,aa_samples=aa,
                    after_certificate_bytes=len(json.dumps(json_safe(b['certificate']),sort_keys=True).encode()) if b['status']=='COMPLETE' else None)
        report['cases'].append(record)
        Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
        print({k:v for k,v in record.items() if k not in ('samples','aa_samples')},flush=True)
    assert pins==sources();report['finished']=True
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')


if __name__=='__main__':main()
