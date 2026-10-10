"""Native diagram coverage and complete timing scopes for residual windows."""
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
from normal_orbit_research.lex import corpus
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
CORPUS=ROOT.parent/'synthesis/data/cocycle-reuse-audit.json'
BASELINE='6c35c3e5326fba834fe08fa1d2fd083378909859'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_seed.py'
    code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('fastunknot._sector_window_baseline');module.__package__='fastunknot'
    sys.modules[module.__name__]=module
    exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
    return module.normal_seed_decide,sha256(code).hexdigest()


def pins():
    result=seeds.sources();result[str(CORPUS.relative_to(ROOT.parent))]=sha256(CORPUS.read_bytes()).hexdigest()
    return result


def audit(old,fresh):
    rows=[];proofs=[];new_proofs=[];regina_checks=0
    for source in corpus():
        diagram=Diagram.from_pd(source['pd']);before=old(diagram)
        disabled=normal_seed_decide(diagram,sector_radius=0)
        assert before==disabled
        after=normal_seed_decide(diagram,sector_radius=2)
        if after['status']=='UNKNOT':
            assert source['expected']=='UNKNOT'and verify_normal_seed_certificate(diagram,after['certificate'])
            proofs.append(after['certificate'])
        added=after['status']=='UNKNOT'and before['status']!='UNKNOT'
        if added:
            proof=after['certificate'];new_proofs.append(proof)
            if fresh:
                surface=regina_surface(regina_triangulation(proof['triangulation']),proof['coordinates'])
                assert surface.isCompressingDisc(True)
                regina_checks+=1
        row=dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],added_positive=added,
            new_stages=after['stages'],window_stats=after['stats'].get('sector_search'),
            reason=after.get('reason'),certificate=after.get('certificate'))
        rows.append(row)
        print(source['name'],before['status'],after['status'],after['work'],
              row['window_stats'].get('sectors_queried')if row['window_stats']else None,flush=True)
    return dict(source_cases=rows,legacy_exact_comparisons=len(rows),source_proofs=proofs,
        added_positive_proofs=new_proofs,old_positives=sum(r['old_status']=='UNKNOT'for r in rows),
        new_positives=sum(r['new_status']=='UNKNOT'for r in rows),fresh_regina_added_discs=regina_checks)


def benchmark(rounds):
    sources={s['name']:s for s in corpus()}
    sources['figure-eight']=dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
    names=('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')
    cases=[('seed/'+name,('seed',sources[name]))for name in names]
    cases += [('recognition/'+name,('recognition',sources[name]))for name in names]
    def run(case,use_old):
        kind,source=case;diagram=Diagram.from_pd(source['pd'])
        if kind=='seed':
            answer=normal_seed_decide(diagram,sector_radius=0 if use_old else 2,max_work=None)
            if answer['status']=='UNKNOT':assert verify_normal_seed_certificate(diagram,answer['certificate'])
            assert 'exhausted'not in answer.get('reason','')
            wire=seeds.encode(answer)
            return dict(completed=True,status=answer['status'],work=answer['work'],
                result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire),
                sectors=answer['stats'].get('sector_search',{}).get('sectors_queried'))
        answer=recognize(diagram,**dict(seeds.FORCED,normal_seed_sector_radius=0 if use_old else 2,seconds=30))
        assert answer.status==source['expected']
        wire=seeds.encode(answer.evidence)
        return dict(completed=True,status=answer.status,method=answer.method,
            evidence_bytes=len(wire),evidence_sha256=sha256(wire).hexdigest())
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']for v in values)
        if row['name'].startswith('seed/'):
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
    old,h=baseline();before=pins();start=time.perf_counter()
    answer=audit(old,args.fresh_regina)if args.mode=='audit'else benchmark(args.rounds)
    assert before==pins();answer.update(native_source_sha256=before,native_baseline=BASELINE,
        native_baseline_source_sha256=h,native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(answer),indent=2)+'\n')
    print('complete',args.mode,answer['native_seconds'],flush=True)


if __name__=='__main__':main()
