"""Audit and measure a checkpoint-bounded bidirectional AHT restart policy."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import random
import time

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.integer_codec import json_safe
from normal_orbit_research import direction, seeds
from normal_orbit_research.coorientation import encoded, topology, expected
from normal_orbit_research.fixtures import layered_torus
from tests.test_interval_orbits import explicit_components, random_pairings
from tests.test_interval_race import measured, switch_fixture

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
BASELINE='cb26c81af813561a174920c7dcb92db57d8b81e3'


def race_stats(answer):
    queries=[q['stats'] for q in answer['queries'].values() if 'race_attempts' in q['stats']]
    return {key:sum(q[key] for q in queries) for key in ('race_attempts','race_restarts','race_checkpoint_work',
        'race_startup_work','race_forward_cycles','race_reverse_cycles','race_winning_cycles')}


def audit(old):
    records=[];saved={};normal_restarts=0
    for number,(case,raw,coords) in enumerate(direction.corpus()):
        for classify in (False,True):
            for reduce in (False,True):
                options=dict(record_certificate=True,classify_boundary=classify,reduce_multiplicity=reduce)
                before=old['normal_surface_orbits'].normal_surface_topology(raw,coords,**options)
                assert before==normal_surface_topology(raw,coords,**options)
                after=normal_surface_topology(raw,coords,sweep_direction='race',**options)
                assert topology(before)==topology(after)
                assert all(after[k]==v for k,v in expected(case['expected'],classify).items())
                assert old['normal_surface_verify'].verify_normal_surface_certificate(raw,coords,before['certificate'])
                assert verify_normal_surface_certificate(raw,coords,before['certificate'])
                assert verify_normal_surface_certificate(raw,coords,after['certificate'])
                stats=race_stats(after);normal_restarts+=stats['race_restarts']
                records.append(dict(case_id=case['id'],classify_boundary=classify,reduce_multiplicity=reduce,
                    old=direction.metrics(before),new=direction.metrics(after),race=stats))
                key=(case['category'],classify,stats['race_restarts']>0)
                if key not in saved:saved[key]=dict(case_id=case['id'],triangulation=raw,coordinates=coords,certificate=after['certificate'])
        if number%200==0:print(number,'of 1275',flush=True)
    rng=random.Random(261009522);systems=[]
    for _ in range(500):
        n=rng.randrange(1,100);systems.append((n,random_pairings(rng,n,rng.randrange(30))))
    for _ in range(100):
        n=rng.randrange(20,100);pairs=[IntervalPairing(a,a,b,b) for a,b in
            ((rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(n,3*n)))]
        systems.append((n,pairs))
    systems += [(n,[IntervalPairing(0,0,i,i) for i in range(1,n)]) for n in (16,32,64,128)]
    systems.append(switch_fixture())
    rows=[];fixtures=[];legacy_comparisons=0
    for i,(n,pairs) in enumerate(systems):
        literal=len(set(explicit_components(n,pairs)))
        for rule in ('aht','fine_wilf'):
            fixed=[measured(n,pairs,d,periodic_rule=rule,record_certificate=True) for d in ('forward','reverse')]
            for d in ('forward','reverse','wide'):
                before=old['interval_orbits'].count_orbits(n,pairs,sweep_direction=d,periodic_rule=rule,record_certificate=True)
                after=count_orbits(n,pairs,sweep_direction=d,periodic_rule=rule,record_certificate=True)
                assert (before.orbits,before.cycles,before.stats,before.certificate)==(after.orbits,after.cycles,after.stats,after.certificate)
                legacy_comparisons+=1
            result,actual_work=measured(n,pairs,'race',periodic_rule=rule,record_certificate=True)
            s=result.stats;winner=s['race_winning_direction'];initial=s['race_initial_allowance'];optimum=min(w for _,w in fixed)
            cap=initial;rounds=0
            while cap<optimum:cap*=2;rounds+=1
            assert s['race_final_allowance']==cap
            bound=4*cap-2*initial+2*rounds+1
            assert s['race_checkpoint_work']<=bound<=12*max(initial,optimum)
            assert actual_work==s['race_checkpoint_work']+s['race_startup_work']
            assert result.orbits==literal and result.certificate==fixed[winner][0].certificate
            assert verify_orbit_certificate(n,pairs,result.certificate)
            rows.append(dict(system=i,points=n,pairings=len(pairs),rule=rule,orbits=literal,
                fixed_work=[w for _,w in fixed],actual_checkpoint_work=actual_work,attempt_bound=bound,
                cycles=result.cycles,stats=s))
            if i>=len(systems)-5:
                fixtures.append(dict(system=i,size=n,pairings=[[p.a,p.b,p.c,p.d,p.reverse] for p in pairs],
                    rule=rule,certificate=result.certificate,stats=s,cycles=result.cycles))
    return dict(normal_cases=records,normal_restarts=normal_restarts,examples=list(saved.values()),
                interval_cases=rows,legacy_interval_comparisons=legacy_comparisons,fixtures=fixtures)


def benchmark(old,rounds):
    inputs=[]
    for n in (16,64,256):
        raw,coords=layered_torus(n);inputs.append((f'layered-{n}',[(raw,coords)]))
    raw,_=layered_torus(1)
    for name,coords in [('empty',[[0]*7]),('mobius',[[0,0,0,0,0,1,0]]),('vertex-link',[[1,1,1,1,0,0,0]])]:
        inputs.append((name,[(raw,coords)]))
    corpus=direction.corpus()
    for label in ('finite_figureEight_relabel_1:6','interior_finite_trefoil:97'):
        _,raw,coords=next(c for c in corpus if c[0]['id']==label);inputs.append((label,[(raw,coords)]))
    inputs.append(('1275-supplied-surfaces',[(raw,coords) for _,raw,coords in corpus]))
    cases=[('forward/'+name,('normal','forward',source)) for name,source in inputs]
    for name,source in inputs:
        if name in ('layered-256','finite_figureEight_relabel_1:6','1275-supplied-surfaces'):
            cases.append(('wide/'+name,('normal','wide',source)))
    cases += [('kernel/star-64',('kernel','wide',(64,[IntervalPairing(0,0,i,i) for i in range(1,64)]))),
              ('kernel/real-switch',('kernel','wide',switch_fixture()))]
    def run(case,use_old):
        kind,reference,inputs=case
        if kind=='kernel':
            n,pairs=inputs
            result=(old['interval_orbits'].count_orbits if use_old else count_orbits)(n,pairs,
                sweep_direction=reference if use_old else 'race',record_certificate=True)
            assert (old['interval_orbit_verify'].verify_orbit_certificate if use_old else verify_orbit_certificate)(n,pairs,result.certificate)
            wire=encoded(result.certificate)
            return dict(completed=result.complete,kind=kind,reference=reference,surfaces=0,
                topology_sha256=sha256(encoded(result.orbits)).hexdigest(),certificate_sha256=sha256(wire).hexdigest(),
                proof_bytes=len(wire),cycles=result.cycles,events=len(result.certificate['operations']),
                restarts=result.stats.get('race_restarts',0),checkpoint_work=result.stats.get('race_checkpoint_work',0))
        produce=(old['normal_surface_orbits'].normal_surface_topology if use_old else normal_surface_topology)
        verify=(old['normal_surface_verify'].verify_normal_surface_certificate if use_old else verify_normal_surface_certificate)
        ph,th=sha256(),sha256();size=cycles=events=restarts=work=0
        for raw,coords in inputs:
            result=produce(raw,coords,sweep_direction=reference if use_old else 'race',record_certificate=True)
            assert result['status']=='COMPLETE' and verify(raw,coords,result['certificate'])
            wire=encoded(result['certificate']);ph.update(wire);th.update(encoded(topology(result)))
            size+=len(wire);cycles+=result['cycles'];events+=sum(len(p['operations']) for p in result['certificate']['queries'].values())
            if not use_old:
                stats=race_stats(result);restarts+=stats['race_restarts'];work+=stats['race_checkpoint_work']
        return dict(completed=True,kind=kind,reference=reference,surfaces=len(inputs),topology_sha256=th.hexdigest(),
            certificate_sha256=ph.hexdigest(),proof_bytes=size,cycles=cycles,events=events,restarts=restarts,checkpoint_work=work)
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        records=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['topology_sha256']==records[0]['topology_sha256'] for v in records)
        for arm in ('old','new'):
            records=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                     for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==records[0] for v in records)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,hashes=direction.baseline(BASELINE);sources=direction.pins();start=time.perf_counter()
    result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    assert sources==direction.pins()
    result.update(baseline=BASELINE,baseline_source_sha256=hashes,source_sha256=sources,seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
