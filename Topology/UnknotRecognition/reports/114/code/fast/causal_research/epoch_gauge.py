"""Periodic exact vertex gauges versus frozen strict-descent epochs."""
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
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from causal_research.epochs import cases
from causal_research.native import FORCED
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
BASELINE='cf4badd87162c7217786228bda3760161367d5e9'
PRIOR=ROOT.parent/'synthesis/data/pachner-epochs-audit.json'


def baseline():
    modules={};hashes={}
    for name in ('pachner_epochs','recognize'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT);hashes[name]=sha256(code).hexdigest()
        if name=='recognize':code=code.replace(b'from .pachner_epochs import',b'from ._epoch_gauge_baseline_pachner_epochs import')
        module=ModuleType('fastunknot._epoch_gauge_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__);modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources();result[str(PRIOR.relative_to(ROOT.parent))]=sha256(PRIOR.read_bytes()).hexdigest()
    return result


def audit(old,fresh):
    records=[];proofs=[];regina_checks=0
    options=dict(max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=2000000,shellings=True,optimize=True)
    for source in cases():
        d=Diagram.from_pd(source['pd']);before=old['pachner_epochs'].pachner_epoch_seed_decide(d,**options)
        after=pachner_epoch_seed_decide(d,regauge_interval=4,**options)
        for r in (before,after):
            if r['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify_transport_disk_certificate(d,r['certificate'])
        if after['status']=='UNKNOT':
            proof=after['certificate'];proofs.append(proof)
            if fresh:
                moves=[s for s in proof['steps']if 'transport'in s]
                raw=moves[-1]['triangulation']if moves else(proof['shelling']['triangulation']if proof['shelling']else proof['source_triangulation'])
                assert regina_surface(regina_triangulation(raw),proof['coordinates']).isCompressingDisc(True);regina_checks+=1
        previous=old['recognize'].recognize(d,**FORCED);disabled=recognize(d,**FORCED)
        assert previous.status==disabled.status==source['expected']
        assert previous.method==disabled.method and previous.evidence==disabled.evidence
        fallback=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64,
            pachner_seed_regauge_interval=4,pachner_seed_max_work=0)
        assert fallback.status==source['expected']
        enabled=None
        if source['name']=='genus-one-miss':
            enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_regauge_interval=4)
            assert enabled.method=='native-pachner-epochs'and verify_transport_disk_certificate(d,enabled.evidence['pachner_seed']['certificate'])
        records.append(dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],old_stats=before['stats'],new_stats=after['stats'],
            certificate=after.get('certificate'),disabled_status=disabled.status,enabled_capped_status=fallback.status,
            enabled_positive_method=None if enabled is None else enabled.method))
        print(source['name'],before['status'],after['status'],before['stats']['epochs'],after['stats']['epochs'],after['work'],flush=True)
    return dict(diagram_cases=records,diagram_proofs=proofs,fresh_regina_disc_checks=regina_checks,disabled_exact_cases=len(records),
        policy=dict(regauge_interval=4,max_upward_per_epoch=1,max_epochs=64,max_work=2000000))


def benchmark(old,rounds):
    cohort={s['name']:s for s in cases()}
    items=[('native/'+n,('native',cohort[n]))for n in ('empty-circle','genus-one-miss','trefoil')]
    items.append(('recognition/genus-one-miss',('recognition',cohort['genus-one-miss'])))
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='native':
            options=dict(max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=1000000,shellings=True,optimize=True)
            r=old['pachner_epochs'].pachner_epoch_seed_decide(d,**options)if use_old else pachner_epoch_seed_decide(d,regauge_interval=4,**options)
            if r['status']=='UNKNOT':assert verify_transport_disk_certificate(d,r['certificate'])
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],work=r['work'],result_bytes=len(wire),stats=r['stats'],
                certificate_sha256=sha256(seeds.encode(r.get('certificate'))).hexdigest())
        call=old['recognize'].recognize if use_old else recognize
        options=dict(FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_max_work=1000000)
        if not use_old:options['pachner_seed_regauge_interval']=4
        r=call(d,**options);assert r.status==source['expected'];wire=seeds.encode(r.evidence)
        return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
    result=seeds.rounds(items,run,rounds)
    result['scope']='Frozen ungauged/current periodic-gauge strict-epoch policy at the same shared node/work allowance; prep, gauge optimization/replay, configured caps, full positive chain replay and serialization included.'
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
