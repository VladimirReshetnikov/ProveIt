"""Source-replayed primitive annulus caps in explicit epoch search."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType

from fastunknot import Diagram,recognize
from fastunknot.pachner_epochs import pachner_epoch_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate,verify_transport_annulus_certificate
from causal_research.epochs import cases
from causal_research.native import FORCED
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
BASELINE='8967fd2bb75b3926869b46b13b516e14598569c4'
PRIOR=ROOT.parent/'synthesis/data/epoch-gauge-audit.json'


def baseline():
    modules={};hashes={}
    for name in ('pachner_epochs','recognize'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT);hashes[name]=sha256(code).hexdigest()
        if name=='recognize':code=code.replace(b'from .pachner_epochs import',b'from ._annulus_baseline_pachner_epochs import')
        module=ModuleType('fastunknot._annulus_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__);modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources();result[str(PRIOR.relative_to(ROOT.parent))]=sha256(PRIOR.read_bytes()).hexdigest();return result


def verify(d,proof):
    return verify_transport_annulus_certificate(d,proof)if proof['schema']=='diagram-transport-annulus-v1'else verify_transport_disk_certificate(d,proof)


def final_surface(proof):
    if proof['schema']=='diagram-transport-annulus-v1':
        return proof['surface_certificate']['triangulation'],proof['surface_certificate']['coordinates'],'annulus'
    moves=[s for s in proof['steps']if 'transport'in s]
    raw=moves[-1]['triangulation']if moves else(proof['shelling']['triangulation']if proof['shelling']else proof['source_triangulation'])
    return raw,proof['coordinates'],'disc'


def audit(old,fresh):
    records=[];proofs=[];regina_checks=[]
    options=dict(max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=2000000,
        shellings=True,optimize=True,regauge_interval=4)
    for source in cases():
        d=Diagram.from_pd(source['pd']);before=old['pachner_epochs'].pachner_epoch_seed_decide(d,**options)
        after=pachner_epoch_seed_decide(d,annulus_caps=True,**options)
        for r in (before,after):
            if r['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify(d,r['certificate'])
        if after['status']=='UNKNOT':
            p=after['certificate'];proofs.append(p)
            if fresh:
                raw,coords,kind=final_surface(p);surface=regina_surface(regina_triangulation(raw),coords)
                if kind=='annulus':assert surface.isConnected()and surface.isOrientable()and int(str(surface.eulerChar()))==0 and surface.countBoundaries()==2
                else:assert surface.isCompressingDisc(True)
                regina_checks.append(dict(name=source['name'],kind=kind,accepted=True))
        previous=old['recognize'].recognize(d,**FORCED);disabled=recognize(d,**FORCED)
        assert previous.status==disabled.status==source['expected']and previous.method==disabled.method and previous.evidence==disabled.evidence
        fallback=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_annulus=True,pachner_seed_max_work=0)
        assert fallback.status==source['expected']
        enabled=None
        if source['name']=='optimized-positive':
            enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_regauge_interval=4,pachner_seed_annulus=True)
            assert enabled.method=='native-pachner-annulus'and verify(d,enabled.evidence['pachner_seed']['certificate'])
        records.append(dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],old_stats=before['stats'],new_stats=after['stats'],
            certificate=after.get('certificate'),disabled_status=disabled.status,enabled_capped_status=fallback.status,
            enabled_positive_method=None if enabled is None else enabled.method))
        print(source['name'],before['status'],after['status'],after['work'],after['stats']['epochs'],flush=True)
    assert any(r['source']['name']=='optimized-positive'and r['old_status']=='INCONCLUSIVE'and r['new_status']=='UNKNOT'for r in records)
    return dict(diagram_cases=records,diagram_proofs=proofs,fresh_regina_checks=regina_checks,disabled_exact_cases=len(records),
        policy=dict(annulus_caps=True,regauge_interval=4,max_upward_per_epoch=1,max_epochs=64,max_work=2000000))


def benchmark(old,rounds):
    cohort={s['name']:s for s in cases()}
    items=[('native/'+n,('native',cohort[n]))for n in ('empty-circle','optimized-positive','genus-one-miss')]
    items.append(('recognition/optimized-positive',('recognition',cohort['optimized-positive'])))
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='native':
            options=dict(max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=1000000,
                shellings=True,optimize=True,regauge_interval=4)
            r=old['pachner_epochs'].pachner_epoch_seed_decide(d,**options)if use_old else pachner_epoch_seed_decide(d,annulus_caps=True,**options)
            if r['status']=='UNKNOT':assert verify(d,r['certificate'])
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],method=r['method'],work=r['work'],result_bytes=len(wire),stats=r['stats'],
                certificate_sha256=sha256(seeds.encode(r.get('certificate'))).hexdigest())
        call=old['recognize'].recognize if use_old else recognize
        options=dict(FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_regauge_interval=4,pachner_seed_max_work=1000000)
        if not use_old:options['pachner_seed_annulus']=True
        r=call(d,**options);assert r.status==source['expected'];wire=seeds.encode(r.evidence)
        return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
    result=seeds.rounds(items,run,rounds)
    result['scope']='Frozen disc-only/current authenticated annulus-or-disc endpoint policy at shared node/work limits; prep, primitive/connectivity arithmetic, complete configured caps, original source-chain replay and serialization included.'
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=3);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();start=time.perf_counter()
    result=audit(old,args.fresh_regina)if args.mode=='audit'else benchmark(old,args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,native_baseline_source_sha256=hashes,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
