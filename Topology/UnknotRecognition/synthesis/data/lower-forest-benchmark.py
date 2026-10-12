"""Source/adaptive lower-forest cut queries, independent replay and paired controls."""
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
    for name in ('core_handlebody','core_three_handle_reduction','bundle_boundary_kernel','bundle_boundary_kernel_verify','normal_cut_handlebodies','normal_cut_handlebodies_verify'):
        key='fastunknot._lower_baseline_'+name
        spec=importlib.util.spec_from_file_location(key,DATA/'lower-forest-baseline'/(name+'.py'))
        m=importlib.util.module_from_spec(spec);sys.modules[key]=m;spec.loader.exec_module(m);modules[name]=m
    modules['normal_cut_handlebodies'].reduce_core_three_handles=modules['core_three_handle_reduction'].reduce_core_three_handles
    modules['normal_cut_handlebodies'].core_handlebody_certificate=modules['core_handlebody'].core_handlebody_certificate
    modules['normal_cut_handlebodies'].bundle_boundary_kernel=modules['bundle_boundary_kernel'].bundle_boundary_kernel
    modules['normal_cut_handlebodies_verify'].replay_bundle_boundary_kernel=modules['bundle_boundary_kernel_verify'].replay_bundle_boundary_kernel
    return modules['normal_cut_handlebodies'].normal_cut_handlebodies, modules['normal_cut_handlebodies_verify'].verify_normal_cut_handlebodies


def main():
    pins=sources();old,old_verify=baseline()
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    ids=['pilot/lst_4_7/0','interior_1_2/mixed','fibonacci_lst_09/mixed',
         'nested_1_4_12/empty','pilot/fibonacci_lst_04/0','pilot/fibonacci_lst_08/0',
         'pilot/finite_trefoil/0','pilot/finite_figureEight/0']
    report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                baseline_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (DATA/'lower-forest-baseline').glob('*.py')},
                corpus_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                python=sys.version,platform=platform.platform(),seed=261012110,cases=[])
    rng=random.Random(report['seed'])
    def query(c,method):
        start=time.perf_counter()
        r=(old if method=='source' else normal_cut_handlebodies)(c['triangulation'],c['coordinates'],record_certificate=True)
        produced=time.perf_counter()
        if r['status']=='COMPLETE':assert (old_verify if method=='source' else verify_normal_cut_handlebodies)(c['triangulation'],c['coordinates'],r['certificate'])
        end=time.perf_counter()
        return r,dict(produce=produced-start,replay=end-produced,total=end-start)
    for key in ids:
        c=next(c for c in bank if c['id']==key)
        a,_=query(c,'source');b,_=query(c,'adaptive')
        shared=a['status']==b['status']=='COMPLETE'
        if shared:assert a['census']==b['census']
        samples=[];aa=[]
        for _ in range(5):
            order=['source','adaptive'];rng.shuffle(order);s=dict(order=order)
            for mode in order:
                r,t=query(c,mode);assert r['status']==(a if mode=='source' else b)['status'];s[mode]=t
            samples.append(s)
        for _ in range(3):
            _,a1=query(c,'source');_,a2=query(c,'source');aa.append(dict(first=a1['total'],second=a2['total'],ratio=a1['total']/a2['total']))
        record=dict(id=key,source_status=a['status'],adaptive_status=b['status'],comparable_successes=shared,
                    source_median=statistics.median(s['source']['total'] for s in samples),
                    adaptive_median=statistics.median(s['adaptive']['total'] for s in samples),
                    paired_speedup=statistics.median(s['source']['total']/s['adaptive']['total'] for s in samples) if shared else None,
                    aa_median=statistics.median(s['ratio'] for s in aa),samples=samples,aa_samples=aa,
                    adaptive_certificate_bytes=len(json.dumps(json_safe(b['certificate']),sort_keys=True).encode()) if b['status']=='COMPLETE' else None)
        report['cases'].append(record)
        Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
        print({k:v for k,v in record.items() if k not in ('samples','aa_samples')},flush=True)
    assert pins==sources();report['finished']=True
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')


if __name__=='__main__':main()
