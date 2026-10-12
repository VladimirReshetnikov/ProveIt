"""Audit and measure finite normal-surface double-cover certificates."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from types import ModuleType

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _TOPOLOGY_FIELDS, _BOUNDARY_FIELDS
from normal_orbit_research.fixtures import layered_torus, regina_triangulation, regina_surface
from normal_orbit_research import seeds

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
CORPUS=ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'
BASELINE='7d9a6f60824a2fbc7e2a3421b7a74f3abb67387d'


def baseline():
    modules=[];hashes={}
    for name in ('normal_surface_orbits','normal_surface_verify'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        module=ModuleType('_coorientation_old_'+name);module.__package__='fastunknot'
        exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
        modules.append(module);hashes[name]=sha256(code).hexdigest()
    return modules[0].normal_surface_topology,modules[1].verify_normal_surface_certificate,hashes


def topology(answer):
    return {k:answer[k] for k in _TOPOLOGY_FIELDS+_BOUNDARY_FIELDS if k in answer}


def encoded(proof):
    return json.dumps(json_safe(proof),sort_keys=True,separators=(',',':')).encode()


def expected(record, classify):
    parts=record['component_records']
    orientable=sum(p['multiplicity'] for p in parts if p['orientable'])
    result=dict(components=record['components'],orientable_components=orientable,
                nonorientable_components=record['components']-orientable,
                boundary_components=record['boundary_components'],
                euler_characteristic=record['euler_characteristic'],normal_disks=record['normal_disks'],
                compressing_disk=record['components']==1 and record['contains_compressing_disk'])
    if classify:
        touched=sum(p['multiplicity'] for p in parts if p['boundary_components'])
        touched_o=sum(p['multiplicity'] for p in parts if p['boundary_components'] and p['orientable'])
        result.update(components_with_boundary=touched,closed_components=record['components']-touched,
                      orientable_components_with_boundary=touched_o,nonorientable_components_with_boundary=touched-touched_o,
                      closed_orientable_components=orientable-touched_o,
                      closed_nonorientable_components=record['components']-orientable-touched+touched_o)
    return result


def audit(old,old_check):
    corpus=json.loads(CORPUS.read_text())
    raw_by_id={r['id']:r['triangulation'] for r in corpus['triangulations']}
    native_by_id={key:regina_triangulation(raw) for key,raw in raw_by_id.items()}
    rows=[];saved={};categories=Counter();regina_checks=0
    for number,case in enumerate(corpus['cases']):
        raw,coords=raw_by_id[case['triangulation_id']],case['coordinates']
        native=regina_surface(native_by_id[case['triangulation_id']],coords)
        parts=native.components();ref=case['expected']
        assert len(parts)==ref['components']
        assert sum(s.isOrientable() for s in parts)==expected(ref,False)['orientable_components']
        assert native.countBoundaries()==ref['boundary_components']
        assert int(str(native.eulerChar()))==ref['euler_characteristic']
        regina_checks+=1
        for classify in (False,True):
            for reduce in (False,True):
                options=dict(classify_boundary=classify,reduce_multiplicity=reduce,record_certificate=True)
                before=old(raw,coords,**options)
                disabled=normal_surface_topology(raw,coords,coorientation=False,**options)
                assert disabled==before,(case['id'],classify,reduce)
                after=normal_surface_topology(raw,coords,**options)
                assert topology(after)==topology(before)
                assert all(after[k]==v for k,v in expected(ref,classify).items())
                assert old_check(raw,coords,before['certificate'])
                assert verify_normal_surface_certificate(raw,coords,before['certificate'])
                assert verify_normal_surface_certificate(raw,coords,after['certificate'])
                derived=after['certificate']['schema']=='normal-surface-topology-v4'
                if derived:
                    assert after['nonorientable_components']==0
                    assert after['queries']['double']['cycles']==0
                else:
                    assert after==before
                categories[case['category'],derived]+=1
                key=(case['category'],derived,classify,reduce)
                if key not in saved:
                    saved[key]=dict(case_id=case['id'],triangulation=raw,coordinates=coords,certificate=after['certificate'])
                rows.append(dict(case_id=case['id'],classify_boundary=classify,reduce_multiplicity=reduce,
                                 derived=derived,topology=topology(after),old_cycles=before['cycles'],new_cycles=after['cycles'],
                                 old_events=sum(len(p['operations']) for p in before['certificate']['queries'].values()),
                                 new_events=sum(len(p['operations']) for p in after['certificate']['queries'].values()),
                                 old_proof_bytes=len(encoded(before['certificate'])),new_proof_bytes=len(encoded(after['certificate']))))
        if number%100==0:print(number,'of',len(corpus['cases']),flush=True)
    # A large genuine normal input checks that saved work grows with the input,
    # without expanding the exponentially many normal sheets.
    family=[]
    for n in (4,16,64,256):
        raw,coords=layered_torus(n)
        before=old(raw,coords,record_certificate=True);after=normal_surface_topology(raw,coords,record_certificate=True)
        assert topology(before)==topology(after)
        assert verify_normal_surface_certificate(raw,coords,after['certificate'])
        family.append(dict(tetrahedra=n,old_cycles=before['cycles'],new_cycles=after['cycles'],
                           old_events=sum(len(p['operations']) for p in before['certificate']['queries'].values()),
                           new_events=sum(len(p['operations']) for p in after['certificate']['queries'].values()),
                           sign_entries=len(after['certificate']['queries']['double']['coorientation']['vertex_values']),
                           old_bytes=len(encoded(before['certificate'])),new_bytes=len(encoded(after['certificate']))))
    return dict(cases=rows,regina_comparisons=regina_checks,triangulations=len(raw_by_id),
                derived=sum(r['derived'] for r in rows),legacy_exact_comparisons=len(rows),
                category_counts=[dict(category=k[0],derived=k[1],count=v) for k,v in sorted(categories.items())],
                examples=list(saved.values()),layered_family=family)


def benchmark(old,old_check,rounds):
    corpus=json.loads(CORPUS.read_text());raw_by_id={r['id']:r['triangulation'] for r in corpus['triangulations']}
    cases=[]
    for n in (1,16,64,256):
        raw,coords=layered_torus(n);cases.append((f'layered-{n}',(raw,coords,False)))
    raw,coords=layered_torus(64)
    cases.append(('layered-64-binary-scale',(raw,[[(2**2048+1)*v for v in row] for row in coords],False)))
    raw,_=layered_torus(1)
    for name,coords in [('empty',[[0]*7]),('mobius',[[0,0,0,0,0,1,0]]),
                        ('mobius-double',[[0,0,0,0,0,2,0]]),('vertex-link',[[1,1,1,1,0,0,0]])]:
        cases.append((name,(raw,coords,True)))
    for category in ('sphere_disc_mobius_mixture','sphere_plus_negative_chi'):
        source=next(c for c in corpus['cases'] if c['category']==category and c['expected']['components']>1)
        cases.append((category,(raw_by_id[source['triangulation_id']],source['coordinates'],True)))
    obstruction=json.loads((DATA/'coherent-obstruction-certificate.json').read_text())
    cases.append(('genus-two-coherent',(obstruction['moves'][-1]['triangulation'],obstruction['family_certificate']['coordinates'],True)))
    def run(case,use_old):
        raw,coords,classify=case
        answer=(old if use_old else normal_surface_topology)(raw,coords,record_certificate=True,classify_boundary=classify)
        assert (old_check if use_old else verify_normal_surface_certificate)(raw,coords,answer['certificate'])
        proof=encoded(answer['certificate'])
        return dict(completed=answer['status']=='COMPLETE',topology=topology(answer),cycles=answer['cycles'],
                    certificate_sha256=sha256(proof).hexdigest(),certificate_bytes=len(proof),
                    certificate_events=sum(len(p['operations']) for p in answer['certificate']['queries'].values()),
                    derived=answer['certificate']['schema']=='normal-surface-topology-v4')
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        records=[m for s in row['samples']+row['warmups'] for m in s['measurements'].values()]
        assert all(m['completed'] and m['topology']==records[0]['topology'] for m in records)
        for arm in ('old','new'):
            samples=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                     for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(m==samples[0] for m in samples)
    return result


def pins():
    result=seeds.sources()
    for p in [Path(__file__),CORPUS,DATA/'coherent-obstruction-certificate.json']:
        result[str(p.relative_to(ROOT.parent))]=sha256(p.read_bytes()).hexdigest()
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,old_check,hashes=baseline();source_pins=pins();start=time.perf_counter()
    result=audit(old,old_check) if args.mode=='audit' else benchmark(old,old_check,args.rounds)
    assert source_pins==pins()
    result.update(mode=args.mode,baseline=BASELINE,baseline_source_sha256=hashes,
                  source_sha256=source_pins,seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
