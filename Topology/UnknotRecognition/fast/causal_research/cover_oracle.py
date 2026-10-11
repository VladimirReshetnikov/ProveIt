"""Compare exact on-demand covers with the frozen indexed native release."""
import argparse
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
from fastunknot.pachner_cover_search import search_pachner_cover,find_pachner_descent
from fastunknot.pachner_cover_verify import verify_pachner_cover,inspect_pachner_descent
import fastunknot.pachner_cover_search as current_cover
from causal_research.fixtures import descent_gadgets
from causal_research.native import diagram_cases,FORCED
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
BASELINE='ce7fb0737a31636e97859fdde19f18c0e42d486b'
PRIOR=ROOT.parent/'synthesis/data/pachner-native-audit.json'


def baseline():
    modules={};hashes={}
    for name in ('pachner_cover_search','normal_pachner_search','recognize'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT);hashes[name]=sha256(code).hexdigest()
        if name=='normal_pachner_search':code=code.replace(b'from .pachner_cover_search import',b'from ._cover_oracle_baseline_pachner_cover_search import')
        if name=='recognize':code=code.replace(b'from .normal_pachner_search import',b'from ._cover_oracle_baseline_normal_pachner_search import')
        module=ModuleType('fastunknot._cover_oracle_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__);modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources();result[str(PRIOR.relative_to(ROOT.parent))]=sha256(PRIOR.read_bytes()).hexdigest()
    return result


def sources(old,fresh):
    records=[];replays=0
    for k in (1,2):
        fixture=descent_gadgets(k);raw=fixture['triangulation'];h=fixture['heights']
        options=dict(max_region_size=6,max_upward=1,method='sleep',max_nodes=None,collect_endpoints=True)
        before=old['pachner_cover_search'].search_pachner_cover(raw,h,**options)
        after=search_pachner_cover(raw,h,**options)
        assert before['status']==after['status']=='COMPLETE_BOUNDED_COVER_FAMILY'
        assert len(before['endpoints'])==len(after['endpoints'])
        for a,b in zip(before['endpoints'],after['endpoints']):
            assert seeds.encode({key:value for key,value in a.items()if key!='active_initial_tetrahedra'})==seeds.encode(
                {key:value for key,value in b.items()if key!='active_initial_tetrahedra'})
            assert verify_pachner_cover(raw,h,b,max_region_size=6,max_upward=1);replays+=1
        assert before['stats']['nodes']==after['stats']['nodes']
        negative=find_pachner_descent(raw,h,max_upward=0,max_nodes=None)
        assert negative['status']=='COMPLETE_BOUNDED_DESCENT'
        descent=find_pachner_descent(raw,h,max_upward=1,max_nodes=None)
        assert descent['status']=='DESCENT_FOUND'
        replay=inspect_pachner_descent(raw,h,descent['certificate'],max_upward=1);assert replay
        checks=None
        if fresh:
            assert regina_triangulation(raw).isSolidTorus()and regina_triangulation(replay['triangulation']).isSolidTorus()
            checks=dict(before=True,after=True)
        records.append(dict(source=fixture,gadgets=k,old_stats=before['stats'],new_stats=after['stats'],
            endpoints=after['endpoints'],exact_endpoint_proofs=len(after['endpoints']),negative=negative,descent=descent,regina=checks))
        print('source',k,len(after['endpoints']),before['stats']['work'],after['stats']['work'],flush=True)
    return dict(source_cases=records,independent_endpoint_replays=replays)


def observed_adapter(call,cover,diagram,options):
    counts=dict(completed_moves=0);snapshot={};advance=cover._advance
    def traced(*args):
        result=advance(*args);counts['completed_moves']+=1;return result
    if hasattr(cover,'_build_index'):
        build=cover._build_index
        def indexed(*args):
            try:return build(*args)
            finally:snapshot.update(args[4])
        with patch.object(cover,'_advance',side_effect=traced),patch.object(cover,'_build_index',side_effect=indexed):
            answer=call(diagram,**options)
    else:
        with patch.object(cover,'_advance',side_effect=traced):answer=call(diagram,**options)
    return answer,dict(counts,index_partial_stats=snapshot)


def diagrams(old,fresh):
    records=[];proofs=[];regina_checks=0
    options=dict(max_upward=1,max_region_size=6,max_nodes=1000,max_work=200000,shellings=True,optimize=True)
    for source in diagram_cases():
        d=Diagram.from_pd(source['pd'])
        before,bprogress=observed_adapter(old['normal_pachner_search'].pachner_seed_decide,old['pachner_cover_search'],d,options)
        after,aprogress=observed_adapter(pachner_seed_decide,current_cover,d,options)
        for r in (before,after):
            if r['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify_transport_disk_certificate(d,r['certificate'])
        if after['status']=='UNKNOT':
            proof=after['certificate'];proofs.append(proof)
            if fresh:
                raw=proof['steps'][-1]['triangulation']if proof['steps']else(
                    proof['shelling']['triangulation']if proof['shelling']else proof['source_triangulation'])
                assert regina_surface(regina_triangulation(raw),proof['coordinates']).isCompressingDisc(True);regina_checks+=1
        disabled_old=old['recognize'].recognize(d,**FORCED)
        disabled=recognize(d,**FORCED)
        enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_max_work=200000)
        assert disabled_old.status==disabled.status==enabled.status==source['expected']
        assert disabled_old.method==disabled.method and disabled_old.evidence==disabled.evidence
        records.append(dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],old_progress=bprogress,new_progress=aprogress,
            old_stats=before['stats'],new_stats=after['stats'],certificate=after.get('certificate'),
            disabled_status=disabled.status,enabled_status=enabled.status,enabled_method=enabled.method))
        print('diagram',source['name'],before['status'],after['status'],bprogress['completed_moves'],aprogress['completed_moves'],flush=True)
    return dict(diagram_cases=records,diagram_proofs=proofs,fresh_regina_disc_checks=regina_checks,disabled_exact_cases=len(records))


def benchmark(old,rounds,diagram):
    if diagram:
        cases={s['name']:s for s in diagram_cases()}
        work=[('native/'+n,('native',cases[n]))for n in ('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')]
        work += [('recognition/'+n,('recognition',cases[n]))for n in ('genus-one-miss','trefoil','figure-eight')]
    else:work=[('descent-'+str(k),('source',descent_gadgets(k)))for k in (1,2)]
    def run(case,use_old):
        kind,value=case
        if kind=='source':
            raw=value['triangulation'];h=value['heights']
            call=old['pachner_cover_search'].find_pachner_descent if use_old else find_pachner_descent
            r=call(raw,h,max_upward=1,max_nodes=None)
            assert r['status']=='DESCENT_FOUND'and inspect_pachner_descent(raw,h,r['certificate'],max_upward=1)
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],nodes=r['stats']['nodes'],work=r['stats']['aggregate_work'],result_bytes=len(wire),stats=r['stats'])
        d=Diagram.from_pd(value['pd'])
        if kind=='native':
            call=old['normal_pachner_search'].pachner_seed_decide if use_old else pachner_seed_decide
            r=call(d,max_upward=1,max_region_size=6,max_nodes=1000,max_work=200000,shellings=True,optimize=True)
            if r['status']=='UNKNOT':assert verify_transport_disk_certificate(d,r['certificate'])
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],work=r['work'],result_bytes=len(wire),stats=r['stats'])
        call=old['recognize'].recognize if use_old else recognize
        r=call(d,**FORCED,use_pachner_seed=True,pachner_seed_max_work=200000)
        assert r.status==value['expected'];wire=seeds.encode(r.evidence)
        return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
    result=seeds.rounds(work,run,rounds)
    result['scope']='Frozen indexed/current on-demand complete first-descent queries or budgeted native/enabled full recognition; prep, configured caps, independent positive replay and serialization charged.'
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','source-benchmark','diagram-benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();start=time.perf_counter()
    result=dict(**sources(old,args.fresh_regina),**diagrams(old,args.fresh_regina))if args.mode=='audit'else benchmark(old,args.rounds,args.mode=='diagram-benchmark')
    assert before==pins();result.update(native_source_sha256=before,native_baseline_source_sha256=hashes,native_baseline=BASELINE,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
