"""Frozen kernel-rebuild baseline and source-bound updated-window evidence."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType

from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.integer_codec import json_safe
from normal_orbit_research import seeds
from normal_orbit_research.sector_windows import corpus
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
PRIOR=ROOT.parent/'synthesis/data/sector-windows-audit.json'
BASELINE='11dde31ee935a556b43e9c06956bb7d3e35cdc3c'


def baseline():
    hashes={};modules={}
    for name in ('sector_residual','normal_seed','recognize'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        hashes[name]=sha256(code).hexdigest()
        if name=='normal_seed':
            code=code.replace(b'from .sector_residual import search_sector_window',
                b'from ._basis_baseline_sector_residual import search_sector_window')
        if name=='recognize':
            code=code.replace(b'from .normal_seed import normal_seed_decide',
                b'from ._basis_baseline_normal_seed import normal_seed_decide')
        module=ModuleType('fastunknot._basis_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
        modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources();result[str(PRIOR.relative_to(ROOT.parent))]=sha256(PRIOR.read_bytes()).hexdigest()
    return result


def audit(old,fresh):
    prior=json.loads(PRIOR.read_text());records=[];proofs=[];regina_checks=0
    for source,previous in zip(corpus(),prior['source_cases']):
        assert seeds.encode(source)==seeds.encode(previous['source'])
        d=Diagram.from_pd(source['pd'])
        # These checks establish exact incumbent disabled behavior afresh;
        # the bounded radius-two incumbent results are retained release data.
        before=old['normal_seed'].normal_seed_decide(d)
        disabled=normal_seed_decide(d,sector_radius=0);assert before==disabled
        after=normal_seed_decide(d,sector_radius=2)
        if after['status']=='UNKNOT':
            assert source['expected']=='UNKNOT'and verify_normal_seed_certificate(d,after['certificate'])
            proofs.append(after['certificate'])
            if fresh and after['certificate']['schema']=='diagram-normal-disc-v1':
                p=after['certificate'];s=regina_surface(regina_triangulation(p['triangulation']),p['coordinates'])
                assert s.isCompressingDisc(True);regina_checks+=1
        r=dict(source=source,disabled_status=before['status'],old_radius_two_status=previous['new_status'],
            new_radius_two_status=after['status'],old_work=previous['new_work'],new_work=after['work'],
            old_window_stats=previous['window_stats'],new_window_stats=after['stats'].get('sector_search'),
            reason=after.get('reason'),certificate=after.get('certificate'))
        records.append(r)
        print(source['name'],r['old_radius_two_status'],r['new_radius_two_status'],after['work'],flush=True)
    return dict(source_cases=records,legacy_exact_comparisons=len(records),source_proofs=proofs,
        old_radius_two_positives=prior['new_positives'],new_radius_two_positives=len(proofs),
        fresh_regina_window_discs=regina_checks,incumbent_radius_two_evidence=str(PRIOR.relative_to(ROOT.parent)))


def benchmark(old,rounds):
    sources={s['name']:s for s in corpus()}
    sources['figure-eight']=dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
    names=('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')
    cases=[('seed/'+name,('seed',sources[name]))for name in names]
    cases += [('recognition/'+name,('recognition',sources[name]))for name in names]
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='seed':
            call=old['normal_seed'].normal_seed_decide if use_old else normal_seed_decide
            answer=call(d,sector_radius=2,max_work=None)
            if answer['status']=='UNKNOT':assert verify_normal_seed_certificate(d,answer['certificate'])
            assert 'exhausted'not in answer.get('reason','')
            wire=seeds.encode(answer)
            return dict(completed=True,status=answer['status'],work=answer['work'],
                result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire),
                certificate_sha256=sha256(seeds.encode(answer.get('certificate'))).hexdigest(),
                window_stats=answer['stats'].get('sector_search'))
        call=old['recognize'].recognize if use_old else recognize
        answer=call(d,**dict(seeds.FORCED,normal_seed_sector_radius=2,seconds=30))
        assert answer.status==source['expected']
        wire=seeds.encode(answer.evidence)
        return dict(completed=True,status=answer.status,method=answer.method,
            evidence_sha256=sha256(wire).hexdigest(),evidence_bytes=len(wire))
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['status']==values[0]['status']for v in values)
        if row['name'].startswith('seed/'):
            assert all(v['certificate_sha256']==values[0]['certificate_sha256']for v in values)
            for arm in ('old','new'):
                values=[{k:v for k,v in s['measurements'][a].items()if k!='seconds'}
                    for s in row['samples']+row['warmups']for a in (arm,arm+'_AA')]
                assert all(v==values[0]for v in values)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();start=time.perf_counter()
    result=audit(old,args.fresh_regina)if args.mode=='audit'else benchmark(old,args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,
        native_baseline_source_sha256=hashes,native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
