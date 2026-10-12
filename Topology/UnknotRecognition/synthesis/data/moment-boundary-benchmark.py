"""Paired complete cut queries: preserved masks versus geometry-reusing moments."""
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
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research.seeds import sources


def baseline(name):
    key='fastunknot._moment_baseline_'+name
    spec=importlib.util.spec_from_file_location(key,DATA/'moment-boundary-baseline'/(name+'.py'))
    module=importlib.util.module_from_spec(spec);sys.modules[key]=module;spec.loader.exec_module(module)
    return getattr(module,'normal_cut_handlebodies' if name=='normal_cut_handlebodies' else 'verify_normal_cut_handlebodies')


def main():
    pins=sources();old=baseline('normal_cut_handlebodies');old_verify=baseline('normal_cut_handlebodies_verify')
    corpus=ROOT/'fast/marked_parallelity_research/corpus.json'
    bank=json.loads(corpus.read_text())['cases']
    selected=[next(c for c in bank if c['id']==key) for key in
        ('pilot/lst_4_7/0','fibonacci_lst_09/mixed','interior_1_2/mixed','finite_figureEight_interior/mixed')]
    raw,rows=layered_torus(2)
    selected.append(dict(id='binary_layered_2_512',triangulation=raw,
                         coordinates=[[(1<<512)*x for x in row] for row in rows]))
    selected.append(dict(id='port_free_layered_2',triangulation=raw,coordinates=[[0]*7 for _ in rows]))
    inherited=ROOT/'fast/marked_parallelity_research/moment_corpus.json'
    for c in json.loads(inherited.read_text())['cases']:
        p=_prepare(c['triangulation'],lambda:None)
        g=_parallelity_geometry(p,_coordinates(p,c['coordinates'],lambda:None),lambda:None)
        if {p['kind'] for p in g['polygons']}=={'edge_cap'}:
            value=old(c['triangulation'],c['coordinates'])
            if value['status']=='COMPLETE':
                selected.append(dict(c,id='cap_only/'+c['id']));break
    assert len(selected)==7
    report=dict(native_source_sha256=pins,python=sys.version,platform=platform.platform(),
                corpus_sha256=hashlib.sha256(corpus.read_bytes()).hexdigest(),
                moment_corpus_sha256=hashlib.sha256(inherited.read_bytes()).hexdigest(),
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                baseline_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sorted((DATA/'moment-boundary-baseline').glob('*.py'))},
                cases=[],seed=26101293,rounds=5)
    rng=random.Random(report['seed']);output=Path(__file__).with_suffix('.json')
    def query(case,method):
        raw,rows=case['triangulation'],case['coordinates'];started=time.perf_counter()
        if method=='masks':result=old(raw,rows,record_certificate=True)
        else:result=normal_cut_handlebodies(raw,rows,record_certificate=True,boundary_method='moments')
        produced=time.perf_counter()
        assert result['status']=='COMPLETE'
        assert (old_verify if method=='masks' else verify_normal_cut_handlebodies)(raw,rows,result['certificate'])
        stopped=time.perf_counter()
        return result,dict(produce=produced-started,replay=stopped-produced,total=stopped-started)
    for c in selected:
        before,_=query(c,'masks');after,_=query(c,'moments')
        assert before['census']==after['census']
        samples=[]
        for _ in range(5):
            order=['masks','moments'];rng.shuffle(order);sample=dict(order=order)
            for method in order:
                value,timing=query(c,method);assert value['census']==before['census']
                sample[method]=timing
            samples.append(sample)
        aa=[]
        for _ in range(3):
            _,first=query(c,'masks');_,second=query(c,'masks')
            aa.append(dict(first=first['total'],second=second['total'],ratio=first['total']/second['total']))
        record=dict(source=c['id'],tetrahedra=len(c['triangulation']['tetrahedra']),
            ports=len(before['certificate']['boundary']['skeleton']['ports']),schema=after['certificate']['schema'],
            histogram=after['census']['histogram'],samples=samples,aa_samples=aa,
            masks_median=statistics.median(s['masks']['total'] for s in samples),
            moments_median=statistics.median(s['moments']['total'] for s in samples),
            paired_speedup=statistics.median(s['masks']['total']/s['moments']['total'] for s in samples),
            aa_median=statistics.median(s['ratio'] for s in aa),
            masks_boundary_stats=before['stats']['boundary'],moments_boundary_stats=after['stats']['boundary'],
            masks_certificate_bytes=len(json.dumps(json_safe(before['certificate']),sort_keys=True).encode()),
            moments_certificate_bytes=len(json.dumps(json_safe(after['certificate']),sort_keys=True).encode()))
        report['cases'].append(record);output.write_text(json.dumps(json_safe(report),indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k not in ('samples','aa_samples','masks_boundary_stats','moments_boundary_stats','histogram')}),flush=True)
    assert sources()==pins
    report['finished']=True;output.write_text(json.dumps(json_safe(report),indent=2)+'\n')


if __name__=='__main__':main()
