"""Native unit-pivot disc counts and fixed-baseline complete-call comparisons."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_disk_kernel import normal_compressing_disk_count,verify_normal_disk_count_certificate
from fastunknot.normal_sector import discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_witness
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import layered_torus

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
CORPUS=ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'
BASELINE='66098968e'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_disk_kernel.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('_unit_ray_old');module.__package__='fastunknot'
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    return module,sha256(source).hexdigest()


def corpus():
    data=json.loads(CORPUS.read_text());tri={r['id']:r['triangulation'] for r in data['triangulations']}
    return [(r,tri[r['triangulation_id']],r['coordinates']) for r in data['cases']]


def audit(old):
    rows=[];saved={}
    for i,(case,raw,coords) in enumerate(corpus()):
        target=sum(r['multiplicity'] for r in case['expected']['component_records'] if r['compressing_disk'])
        for rule in ('fine_wilf','aht'):
            options=dict(periodic_rule=rule,record_certificate=True)
            before=old.normal_compressing_disk_count(raw,coords,**options)
            assert before==normal_compressing_disk_count(raw,coords,unit_ray=False,**options)
            after=normal_compressing_disk_count(raw,coords,**options)
            assert before['compressing_disk_components']==after['compressing_disk_components']==target
            assert old.verify_normal_disk_count_certificate(raw,coords,before['certificate'])
            assert verify_normal_disk_count_certificate(raw,coords,before['certificate'])
            assert verify_normal_disk_count_certificate(raw,coords,after['certificate'])
            ray=after['certificate']['schema']=='normal-disc-count-v2'
            if not ray:assert before==after
            else:assert after['stats']['orbit_cycles']==0
            old_wire,new_wire=seeds.encode(before['certificate']),seeds.encode(after['certificate'])
            rows.append(dict(case_id=case['id'],rule=rule,unit_ray=ray,compressing_disks=target,
                old_cycles=before['stats']['orbit_cycles'],new_cycles=after['stats']['orbit_cycles'],
                old_bytes=len(old_wire),new_bytes=len(new_wire),ray_steps=after['stats'].get('ray_steps',0)))
            key=(case['category'],ray,rule)
            if key not in saved:saved[key]=dict(case_id=case['id'],triangulation=raw,coordinates=coords,
                                               certificate=after['certificate'])
        if i%200==0:print(i,'of 1275',flush=True)
    return dict(cases=rows,legacy_exact_comparisons=2550,unit_cases=sum(r['unit_ray'] for r in rows),examples=list(saved.values()))


def benchmark(old,rounds):
    cases=[]
    for n in (16,64,256):
        raw,coords=layered_torus(n);cases.append((f'count/layered-{n}',('count',raw,coords)))
    raw,coords=layered_torus(64)
    cases.append(('count/layered-64-binary-scale',('count',raw,[[(2**4096+1)*v for v in row] for row in coords])))
    raw,_=layered_torus(1)
    for name,coords in [('empty',[[0]*7]),('one-sided',[[0,0,0,0,0,1,0]]),('vertex-link',[[1,1,1,1,0,0,0]])]:
        cases.append(('count/'+name,('count',raw,coords)))
    records=corpus()
    for category in ('sphere_disc_mobius_mixture','sphere_plus_negative_chi'):
        case,raw,coords=next(r for r in records if r[0]['category']==category and r[0]['expected']['components']>1)
        cases.append(('count/'+category,('count',raw,coords)))
    for n in (16,64):
        raw,coords=layered_torus(n);cases.append((f'sector/layered-{n}',('sector',raw,coords)))
    def run(case,use_old):
        kind,raw,coords=case
        if kind=='count':
            produce,verify=(old.normal_compressing_disk_count,old.verify_normal_disk_count_certificate) if use_old else (
                normal_compressing_disk_count,verify_normal_disk_count_certificate)
            answer=produce(raw,coords,record_certificate=True)
            assert answer['status']=='COMPLETE' and verify(raw,coords,answer['certificate'])
            signature=answer['compressing_disk_components'];cycles=answer['stats']['orbit_cycles']
        else:
            support=[(i,q) for i,row in enumerate(coords) for q in range(3) if row[4+q]]
            if use_old:
                with patch('fastunknot.normal_sector.normal_compressing_disk_count',old.normal_compressing_disk_count):
                    answer=discover_in_sector(raw,support)
            else:answer=discover_in_sector(raw,support)
            assert answer['status']=='DISC_FOUND' and verify_sector_witness(raw,answer['certificate'])
            signature=answer['coordinates'];cycles=None
        wire=seeds.encode(answer['certificate'])
        return dict(completed=True,kind=kind,answer_sha256=sha256(seeds.encode(signature)).hexdigest(),
                    certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),cycles=cycles)
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        records=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['answer_sha256']==records[0]['answer_sha256'] for v in records)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'} for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,old_hash=baseline();pins=seeds.sources()
    for path in (CORPUS,Path(__file__)):
        pins[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    started=time.perf_counter();result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    for p,h in pins.items():assert sha256((ROOT.parent/p).read_bytes()).hexdigest()==h,p
    result.update(source_sha256=pins,baseline=BASELINE,baseline_source_sha256=old_hash,seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
