"""Complete queue/max-weight cut queries with independent replay and paired controls."""
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
    for name in ('core_three_handle_reduction','normal_cut_handlebodies'):
        key='fastunknot._weighted_baseline_'+name
        spec=importlib.util.spec_from_file_location(key,DATA/'weighted-forest-baseline'/(name+'.py'))
        m=importlib.util.module_from_spec(spec);sys.modules[key]=m;spec.loader.exec_module(m);modules[name]=m
    modules['normal_cut_handlebodies'].reduce_core_three_handles=modules['core_three_handle_reduction'].reduce_core_three_handles
    return modules['normal_cut_handlebodies'].normal_cut_handlebodies


def main():
    pins=sources();old=baseline()
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    ids=['pilot/lst_4_7/0','interior_1_2/mixed','finite_figureEight_interior/mixed',
         'pilot/finite_trefoil_interior/0','nested_1_4_12/empty','nested_1_4_12/boundary_link',
         'interior_loop/empty','interior_loop/boundary_link']
    report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                baseline_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (DATA/'weighted-forest-baseline').glob('*.py')},
                corpus_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                python=sys.version,platform=platform.platform(),seed=261012104,cases=[])
    rng=random.Random(report['seed'])
    def query(c,method):
        start=time.perf_counter()
        r=(old if method=='queue' else normal_cut_handlebodies)(c['triangulation'],c['coordinates'],record_certificate=True)
        produced=time.perf_counter()
        if r['status']=='COMPLETE':assert verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],r['certificate'])
        end=time.perf_counter()
        return r,dict(produce=produced-start,replay=end-produced,total=end-start)
    for key in ids:
        c=next(c for c in bank if c['id']==key)
        a,_=query(c,'queue');b,_=query(c,'weighted')
        shared=a['status']==b['status']=='COMPLETE'
        if shared:assert a['census']==b['census']
        samples=[];aa=[]
        for _ in range(5):
            order=['queue','weighted'];rng.shuffle(order);s=dict(order=order)
            for mode in order:
                r,t=query(c,mode);assert r['status']==(a if mode=='queue' else b)['status'];s[mode]=t
            samples.append(s)
        for _ in range(3):
            _,a1=query(c,'queue');_,a2=query(c,'queue');aa.append(dict(first=a1['total'],second=a2['total'],ratio=a1['total']/a2['total']))
        record=dict(id=key,queue_status=a['status'],weighted_status=b['status'],comparable_successes=shared,
                    queue_median=statistics.median(s['queue']['total'] for s in samples),
                    weighted_median=statistics.median(s['weighted']['total'] for s in samples),
                    paired_speedup=statistics.median(s['queue']['total']/s['weighted']['total'] for s in samples) if shared else None,
                    aa_median=statistics.median(s['ratio'] for s in aa),samples=samples,aa_samples=aa,
                    weighted_certificate_bytes=len(json.dumps(json_safe(b['certificate']),sort_keys=True).encode()))
        report['cases'].append(record)
        Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
        print({k:v for k,v in record.items() if k not in ('samples','aa_samples')},flush=True)
    assert pins==sources();report['finished']=True
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')


if __name__=='__main__':main()
