"""Native report-79 integration, exact source audit and complete timings."""
import argparse
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.pachner_regions import search_pachner_regions
from fastunknot.pachner_cover_search import search_pachner_cover,find_pachner_descent
from fastunknot.pachner_cover_verify import verify_pachner_cover,inspect_pachner_descent
from fastunknot.pachner_commitments import _State,_events
from commitment_research.fixtures import canonical_cochain_key
from causal_research.fixtures import descent_gadgets
from normal_orbit_research import seeds
from normal_orbit_research.sector_windows import corpus
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT.parent/'reports/79/repro/fast'
BASELINE='a7ab589dbc856df5e4b3eb797ff2131056f16268'
RUNTIME=('cocycle_transport','cocycle_transport_verify','pachner_commitments',
    'pachner_commitments_verify','pachner_regions','pachner_cover_search',
    'pachner_cover_verify','pachner_causality','normal_transport','normal_transport_verify')
FORCED=dict(seeds.FORCED,use_normal_seed=False,seconds=30)


def pins():
    result=seeds.sources()
    for path in (REPORT/'fastunknot/normal_pachner_search.py',
                 REPORT/'shared_cover_research/results/exhaustion.json'):
        result[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    return result


def delivered():
    path=REPORT/'fastunknot/normal_pachner_search.py';code=path.read_bytes()
    module=ModuleType('fastunknot._delivered_pachner_adapter');module.__package__='fastunknot'
    sys.modules[module.__name__]=module;exec(compile(code,str(path),'exec'),module.__dict__)
    return module.pachner_seed_decide


def previous_recognizer():
    path='Topology/UnknotRecognition/fast/fastunknot/recognize.py'
    code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('fastunknot._before_pachner_recognize');module.__package__='fastunknot'
    sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
    return module.recognize


def endpoint_map(raw,heights,proofs):
    cache={};result={}
    for proof in proofs:
        moves=proof['moves'];after=moves[-1]['triangulation']if moves else raw
        h=moves[-1]['transport']['heights']if moves else heights
        wire=json.dumps((after,[[x-row[0]for x in row]for row in h]),sort_keys=True,separators=(',',':'))
        if wire not in cache:cache[wire]=canonical_cochain_key(after,h)
        result.setdefault(cache[wire],proof)
    return result


def source_audit(fresh):
    records=[];replays=0
    for count in (1,2):
        fixture=descent_gadgets(count);raw=fixture['triangulation'];h=fixture['heights'];n=len(raw['tetrahedra'])
        events=_events(_State(raw,h,tuple(range(n)),0,0,()),True,lambda:None)
        assert not any(e.kind=='down'for e in events)
        options=dict(max_region_size=6,max_upward=1,method='sleep',max_nodes=None,seek_disc=False,collect_endpoints=True)
        old=search_pachner_regions(raw,h,**options);new=search_pachner_cover(raw,h,**options)
        assert old['status']=='COMPLETE_BOUNDED_REGIONS'and new['status']=='COMPLETE_BOUNDED_COVER_FAMILY'
        oldkeys=endpoint_map(raw,h,old['endpoints']);newkeys=endpoint_map(raw,h,new['endpoints'])
        assert oldkeys.keys()==newkeys.keys()
        for p in list(oldkeys.values())+new['endpoints']:
            assert verify_pachner_cover(raw,h,p,max_region_size=6,max_upward=1);replays+=1
        negative=find_pachner_descent(raw,h,max_upward=0,max_nodes=None)
        assert negative['status']=='COMPLETE_BOUNDED_DESCENT'
        descent=find_pachner_descent(raw,h,max_upward=1,max_nodes=None)
        assert descent['status']=='DESCENT_FOUND'
        replay=inspect_pachner_descent(raw,h,descent['certificate'],max_upward=1);assert replay
        assert replay['upward_moves']==1 and replay['downward_moves']==2
        regina_checks=None
        if fresh:
            before=regina_triangulation(raw);after=regina_triangulation(replay['triangulation'])
            assert before.isSolidTorus()and after.isSolidTorus()
            regina_checks=dict(before=True,after=True)
        records.append(dict(gadgets=count,source=fixture,restart_stats=old['stats'],shared_stats=new['stats'],
            exact_endpoint_classes=len(newkeys),restart_representatives=list(oldkeys.values()),
            shared_endpoints=new['endpoints'],zero_upward=negative,descent=descent,regina=regina_checks))
        print('source',count,'endpoints',len(newkeys),'restart/shared',old['stats']['nodes'],new['stats']['nodes'],flush=True)
    return dict(source_cases=records,independent_endpoint_replays=replays)


def diagram_cases():
    allcases=corpus()
    names=('empty-circle','optimized-positive','trefoil','genus-one-miss','survivor-08','survivor-10')
    chosen=[next(s for s in allcases if s['name']==name)for name in names]
    chosen += [s for s in allcases if s['name'].startswith('random-')][:6]
    chosen.append(dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED'))
    return chosen


def diagram_audit(fresh):
    old=delivered();old_recognize=previous_recognizer();records=[];proofs=[];regina_checks=0
    options=dict(max_upward=1,max_region_size=6,max_nodes=1000,max_work=200000,
        shellings=True,optimize=True)
    for source in diagram_cases():
        d=Diagram.from_pd(source['pd']);before=old(d,**options);after=pachner_seed_decide(d,**options)
        for answer in (before,after):
            if answer['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify_transport_disk_certificate(d,answer['certificate'])
        if after['status']=='UNKNOT':
            proofs.append(after['certificate'])
            if fresh:
                p=after['certificate'];raw=p['steps'][-1]['triangulation']if p['steps']else (
                    p['shelling']['triangulation']if p['shelling']else p['source_triangulation'])
                s=regina_surface(regina_triangulation(raw),p['coordinates']);assert s.isCompressingDisc(True);regina_checks+=1
        baseline=old_recognize(d,**FORCED);disabled=recognize(d,**FORCED,use_pachner_seed=False)
        enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_max_work=200000)
        assert baseline.status==disabled.status==enabled.status==source['expected']
        assert baseline.method==disabled.method and baseline.evidence==disabled.evidence
        if 'pachner_seed'in enabled.evidence and enabled.evidence['pachner_seed']['status']=='UNKNOT':
            assert verify_transport_disk_certificate(d,enabled.evidence['pachner_seed']['certificate'])
        records.append(dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],old_stats=before['stats'],new_stats=after['stats'],
            certificate=after.get('certificate'),disabled_status=disabled.status,enabled_status=enabled.status,
            enabled_method=enabled.method))
        print('diagram',source['name'],before['status'],after['status'],enabled.status,flush=True)
    return dict(diagram_cases=records,diagram_proofs=proofs,fresh_regina_disc_checks=regina_checks,
        disabled_exact_cases=len(records))


def audit(fresh):
    for name in RUNTIME:
        assert (ROOT/'fastunknot'/f'{name}.py').read_bytes()==(REPORT/'fastunknot'/f'{name}.py').read_bytes()
    for name in ('pachner23','pachner23_verify','pachner32','pachner32_verify','normal_cocycle','integer_codec'):
        assert (ROOT/'fastunknot'/f'{name}.py').read_bytes()==(REPORT/'fastunknot'/f'{name}.py').read_bytes()
    return dict(**source_audit(fresh),**diagram_audit(fresh),copied_runtime_modules=list(RUNTIME),
        unchanged_foundations=['pachner23','pachner23_verify','pachner32','pachner32_verify','normal_cocycle','integer_codec'])


def source_benchmark(rounds):
    cases=[(f'descent-{k}',descent_gadgets(k))for k in (1,2)]
    def run(fixture,use_old):
        raw=fixture['triangulation'];h=fixture['heights'];n=len(raw['tetrahedra'])
        def smaller(p):return bool(p['moves']and len(p['moves'][-1]['triangulation']['tetrahedra'])<n)
        call=search_pachner_regions if use_old else search_pachner_cover
        r=call(raw,h,max_region_size=6,max_upward=1,method='sleep',max_nodes=None,seek_disc=False,endpoint=smaller)
        assert r['status']=='ENDPOINT_SELECTED'
        replay=inspect_pachner_descent(raw,h,r['certificate'],max_upward=1);assert replay
        wire=seeds.encode(r)
        return dict(completed=True,status='DESCENT_FOUND',nodes=r['stats']['nodes'],work=r['stats']['work'],
            result_bytes=len(wire),loss=n-len(replay['triangulation']['tetrahedra']))
    result=seeds.rounds(cases,run,rounds)
    result['scope']='First verified strict descent on fixed genuine source triangulations; includes source/index/search, independent replay and serialization; not diagram recognition.'
    return result


def diagram_benchmark(rounds):
    old=delivered();sources={s['name']:s for s in diagram_cases()}
    cases=[('native/'+name,('native',sources[name]))for name in ('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')]
    cases += [('recognition/'+name,('recognition',sources[name]))for name in ('empty-circle','genus-one-miss','trefoil','figure-eight')]
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='native':
            call=old if use_old else pachner_seed_decide
            r=call(d,max_upward=1,max_region_size=6,max_nodes=1000,max_work=200000,shellings=True,optimize=True)
            if r['status']=='UNKNOT':assert verify_transport_disk_certificate(d,r['certificate'])
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],work=r['work'],result_bytes=len(wire))
        r=recognize(d,**FORCED,use_pachner_seed=not use_old,pachner_seed_max_work=200000)
        assert r.status==source['expected'];wire=seeds.encode(r.evidence)
        return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
    result=seeds.rounds(cases,run,rounds)
    result['scope']='Native shared-cover adapter versus restarted delivered adapter, and full recognition enabled versus disabled; preparation/replay/serialization included, bounded misses/caps included.'
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','source-benchmark','diagram-benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    before=pins();started=time.perf_counter()
    result=audit(args.fresh_regina)if args.mode=='audit'else source_benchmark(args.rounds)if args.mode=='source-benchmark'else diagram_benchmark(args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),native_seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
