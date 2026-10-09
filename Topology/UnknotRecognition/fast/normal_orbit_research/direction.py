"""Pinned comparisons of forward, reflected and wider-end orbit sweeps."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import random
import subprocess
import sys
import time
from types import ModuleType

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _arc_system
from fastunknot.integer_codec import json_safe
from normal_orbit_research import seeds
from normal_orbit_research.coorientation import CORPUS, encoded, expected, topology
from normal_orbit_research.fixtures import layered_torus
from tests.test_interval_orbits import explicit_components, random_pairings

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
BASELINE='3310e1e84b37f848b5c9911a3725c5881286a0fd'


def baseline():
    modules={};hashes={}
    for name in ('interval_orbits','interval_orbit_verify','normal_surface_orbits','normal_surface_verify'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        module=ModuleType('_direction_old_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module
        exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
        modules[name]=module;hashes[name]=sha256(source).hexdigest()
    # Both use the identical immutable public pairing class. The old search
    # and old replay bodies are frozen independently of current implementations.
    modules['interval_orbits'].IntervalPairing=IntervalPairing
    modules['normal_surface_orbits'].count_orbits=modules['interval_orbits'].count_orbits
    modules['normal_surface_verify'].verify_orbit_certificate=modules['interval_orbit_verify'].verify_orbit_certificate
    return modules,hashes


def corpus():
    data=json.loads(CORPUS.read_text())
    triangulations={r['id']:r['triangulation'] for r in data['triangulations']}
    return [(r,triangulations[r['triangulation_id']],r['coordinates']) for r in data['cases']]


def metrics(answer):
    proof=answer['certificate'];wire=encoded(proof)
    return dict(cycles=answer['cycles'],events=sum(len(p['operations']) for p in proof['queries'].values()),
                bytes=len(wire),reflections=sum(p.get('version') in (3,4) for p in proof['queries'].values()),
                certificate_sha256=sha256(wire).hexdigest())


def audit(old):
    old_normal=old['normal_surface_orbits'].normal_surface_topology
    old_check=old['normal_surface_verify'].verify_normal_surface_certificate
    rows=[];saved={};counterexample=None
    for number,(case,raw,coords) in enumerate(corpus()):
        for classify in (False,True):
            for reduce in (False,True):
                options=dict(record_certificate=True,classify_boundary=classify,reduce_multiplicity=reduce)
                before=old_normal(raw,coords,**options)
                assert before==normal_surface_topology(raw,coords,**options)
                assert old_check(raw,coords,before['certificate'])
                assert verify_normal_surface_certificate(raw,coords,before['certificate'])
                assert all(before[k]==v for k,v in expected(case['expected'],classify).items())
                for direction in ('reverse','wide'):
                    after=normal_surface_topology(raw,coords,sweep_direction=direction,**options)
                    assert topology(after)==topology(before)
                    assert verify_normal_surface_certificate(raw,coords,after['certificate'])
                    previous,current=metrics(before),metrics(after)
                    rows.append(dict(case_id=case['id'],category=case['category'],classify_boundary=classify,
                                     reduce_multiplicity=reduce,direction=direction,old=previous,new=current))
                    key=(case['category'],direction,classify)
                    if key not in saved:
                        saved[key]=dict(case_id=case['id'],direction=direction,triangulation=raw,
                                        coordinates=coords,certificate=after['certificate'])
                    if case['id']=='finite_figureEight_relabel_1:6' and not classify and reduce and direction=='wide':
                        counterexample=dict(triangulation=raw,coordinates=coords,old=before['certificate'],new=after['certificate'],
                                            old_metrics=previous,new_metrics=current)
        if number%200==0:print(number,'of 1275',flush=True)
    rng=random.Random(261009518);random_rows=[]
    for trial in range(1000):
        size=rng.randrange(1,101);pairs=random_pairings(rng,size,rng.randrange(15))
        literal=len(set(explicit_components(size,pairs)))
        for rule in ('aht','fine_wilf'):
            before=old['interval_orbits'].count_orbits(size,pairs,periodic_rule=rule,record_certificate=True)
            forward=count_orbits(size,pairs,periodic_rule=rule,record_certificate=True)
            assert (before.complete,before.orbits,before.cycles,before.stats,before.certificate)==(
                forward.complete,forward.orbits,forward.cycles,forward.stats,forward.certificate)
            for direction in ('reverse','wide'):
                after=count_orbits(size,pairs,periodic_rule=rule,sweep_direction=direction,record_certificate=True)
                assert before.orbits==after.orbits==literal
                assert verify_orbit_certificate(size,pairs,after.certificate)
                random_rows.append(dict(trial=trial,points=size,pairings=len(pairs),rule=rule,direction=direction,
                                        old_cycles=before.cycles,new_cycles=after.cycles,orbits=literal))
    family=[]
    for n in (4,16,64,256):
        raw,coords=layered_torus(n);p=_prepare(raw,lambda:None);a=_coordinates(p,coords,lambda:None);size,pairs=_arc_system(p,a)
        records={}
        for direction in ('forward','reverse','wide'):
            answer=count_orbits(size,pairs,sweep_direction=direction,record_certificate=True)
            assert verify_orbit_certificate(size,pairs,answer.certificate)
            records[direction]=dict(cycles=answer.cycles,events=len(answer.certificate['operations']),
                transmissions=answer.stats['transmissions'],mergers=answer.stats['mergers'],bytes=len(encoded(answer.certificate)))
        family.append(dict(tetrahedra=n,points=size,records=records))
    return dict(configurations=rows,default_exact_comparisons=5100,random_comparisons=random_rows,
                examples=list(saved.values()),counterexample=counterexample,layered_family=family)


def benchmark(old,rounds):
    cases=[]
    for n in (1,16,64,256):
        raw,coords=layered_torus(n);cases.append((f'layered-{n}',[(raw,coords)]))
    raw,coords=layered_torus(64)
    cases.append(('layered-64-binary-scale',[(raw,[[(2**2048+1)*v for v in row] for row in coords])]))
    raw,_=layered_torus(1)
    for name,coords in [('empty',[[0]*7]),('mobius',[[0,0,0,0,0,1,0]]),('vertex-link',[[1,1,1,1,0,0,0]])]:
        cases.append((name,[(raw,coords)]))
    all_inputs=corpus()
    for name in ('finite_figureEight_relabel_1:6','interior_finite_trefoil:97'):
        case,raw,coords=next(c for c in all_inputs if c[0]['id']==name)
        cases.append((name,[(raw,coords)]))
    source=json.loads((DATA/'coherent-obstruction-certificate.json').read_text())
    cases.append(('genus-two-coherent',[(source['moves'][-1]['triangulation'],source['family_certificate']['coordinates'])]))
    cases.append(('1275-supplied-surfaces',[(raw,coords) for _,raw,coords in all_inputs]))
    def run(inputs,use_old):
        produce=(old['normal_surface_orbits'].normal_surface_topology if use_old else normal_surface_topology)
        verify=(old['normal_surface_verify'].verify_normal_surface_certificate if use_old else verify_normal_surface_certificate)
        options={} if use_old else dict(sweep_direction='wide')
        proof_hash,topology_hash=sha256(),sha256();events=cycles=reflections=proof_bytes=0
        for raw,coords in inputs:
            answer=produce(raw,coords,record_certificate=True,**options)
            assert answer['status']=='COMPLETE' and verify(raw,coords,answer['certificate'])
            wire=encoded(answer['certificate']);proof_hash.update(wire)
            topology_hash.update(encoded(topology(answer)))
            events+=sum(len(p['operations']) for p in answer['certificate']['queries'].values())
            cycles+=answer['cycles']
            reflections+=sum(p.get('version') in (3,4) for p in answer['certificate']['queries'].values())
            proof_bytes+=len(wire)
        return dict(completed=True,surfaces=len(inputs),events=events,cycles=cycles,reflections=reflections,
                    proof_bytes=proof_bytes,certificate_sha256=proof_hash.hexdigest(),topology_sha256=topology_hash.hexdigest())
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['topology_sha256']==values[0]['topology_sha256'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    return result


def pins():
    result=seeds.sources()
    for path in (CORPUS,DATA/'coherent-obstruction-certificate.json'):
        result[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,hashes=baseline();sources=pins();start=time.perf_counter()
    result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    assert sources==pins()
    result.update(baseline=BASELINE,baseline_source_sha256=hashes,source_sha256=sources,seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
