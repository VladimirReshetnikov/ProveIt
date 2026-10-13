"""Actual-diagram strict epoch reach and whole-chain source proof evidence."""
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
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from causal_research.native import diagram_cases,FORCED
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
BASELINE='cf3bb3068b107fc2a32241e3e9d79d6bae482427'
PRIOR=ROOT.parent/'synthesis/data/cover-oracle-audit.json'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/recognize.py'
    code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('fastunknot._before_epoch_recognize');module.__package__='fastunknot'
    sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
    return module.recognize,sha256(code).hexdigest()


def pins():
    result=seeds.sources();result[str(PRIOR.relative_to(ROOT.parent))]=sha256(PRIOR.read_bytes()).hexdigest()
    return result


def cases():
    cohort={s['name']:s for s in diagram_cases()}
    selected=[cohort[n]for n in ('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')]
    selected.append(dict(name='one-crossing',pd=Diagram.from_braid(2,[1]).pd,expected='UNKNOT'))
    return selected


def audit(fresh):
    old,_=baseline();records=[];proofs=[];regina_checks=0
    for source in cases():
        d=Diagram.from_pd(source['pd'])
        before=pachner_seed_decide(d,max_upward=1,max_region_size=6,max_nodes=1000,max_work=2000000,shellings=True,optimize=True)
        after=pachner_epoch_seed_decide(d,max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=2000000,shellings=True,optimize=True)
        for r in (before,after):
            if r['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify_transport_disk_certificate(d,r['certificate'])
        if after['status']=='UNKNOT':
            p=after['certificate'];proofs.append(p)
            if fresh:
                raw=p['steps'][-1]['triangulation']if p['steps']else(p['shelling']['triangulation']if p['shelling']else p['source_triangulation'])
                assert regina_surface(regina_triangulation(raw),p['coordinates']).isCompressingDisc(True);regina_checks+=1
        disabled_old=old(d,**FORCED);disabled=recognize(d,**FORCED)
        assert disabled_old.status==disabled.status==source['expected']
        assert disabled_old.method==disabled.method and disabled_old.evidence==disabled.evidence
        # All complete verdicts are checked with a zero local allowance;
        # the successful nonempty epoch proof is exercised through the actual
        # enabled recognizer under its complete practical allowance as well.
        enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64,pachner_seed_max_work=0)
        assert enabled.status==source['expected']
        positive_enabled=None
        if source['name']=='genus-one-miss':
            positive_enabled=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=64)
            assert positive_enabled.status=='UNKNOT'and positive_enabled.method=='native-pachner-epochs'
            assert verify_transport_disk_certificate(d,positive_enabled.evidence['pachner_seed']['certificate'])
        stats=after['stats'];assert stats['epochs']<=stats.get('initial_tetrahedra',stats['epochs'])
        assert all(r['after']<r['before']and r['upward_moves']<=1 for r in stats['epoch_records'])
        records.append(dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],old_stats=before['stats'],new_stats=stats,
            certificate=after.get('certificate'),disabled_status=disabled.status,enabled_capped_status=enabled.status,
            enabled_positive_method=None if positive_enabled is None else positive_enabled.method))
        print(source['name'],before['status'],after['status'],stats['epochs'],after['work'],flush=True)
    assert any(r['source']['name']=='genus-one-miss'and r['old_status']=='INCONCLUSIVE'and r['new_status']=='UNKNOT'for r in records)
    return dict(diagram_cases=records,diagram_proofs=proofs,fresh_regina_disc_checks=regina_checks,
        disabled_exact_cases=len(records),policy=dict(single_search_total_upward=1,epoch_upward_per_round=1,max_epochs=64,max_work=2000000))


def benchmark(rounds):
    cohort={s['name']:s for s in cases()}
    items=[('native/'+n,('native',cohort[n]))for n in ('empty-circle','genus-one-miss','trefoil')]
    items.append(('recognition/genus-one-miss',('recognition',cohort['genus-one-miss'])))
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='native':
            if use_old:r=pachner_seed_decide(d,max_upward=1,max_region_size=6,max_nodes=1000,max_work=1000000,shellings=True,optimize=True)
            else:r=pachner_epoch_seed_decide(d,max_upward_per_epoch=1,max_epochs=64,max_nodes=1000,max_work=1000000,shellings=True,optimize=True)
            if r['status']=='UNKNOT':assert verify_transport_disk_certificate(d,r['certificate'])
            wire=seeds.encode(r)
            return dict(completed=True,status=r['status'],work=r['work'],result_bytes=len(wire),stats=r['stats'],
                certificate_sha256=sha256(seeds.encode(r.get('certificate'))).hexdigest())
        r=recognize(d,**FORCED,use_pachner_seed=True,pachner_seed_epochs=0 if use_old else 64,pachner_seed_max_work=1000000)
        assert r.status==source['expected'];wire=seeds.encode(r.evidence)
        return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
    result=seeds.rounds(items,run,rounds)
    result['scope']='Explicit single total-upward family versus strict per-epoch policy at the same shared work/node allowance; preparation, configured caps, independent positive replay and serialization included. The policies have different reach, not equivalent finite languages.'
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=3);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    _,hashcode=baseline();before=pins();start=time.perf_counter()
    result=audit(args.fresh_regina)if args.mode=='audit'else benchmark(args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,
        frozen_recognizer_sha256=hashcode,native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
