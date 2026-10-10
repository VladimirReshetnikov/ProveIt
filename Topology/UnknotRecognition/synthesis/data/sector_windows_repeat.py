"""Repeat noisy early-positive and complete-recognition A/A controls."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.sector_windows import corpus,pins

parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();sources={s['name']:s for s in corpus()}
sources['figure-eight']=dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
cases=[('seed/optimized-positive',('seed',sources['optimized-positive']))]
cases += [('recognition/'+name,('recognition',sources[name]))for name in ('empty-circle','figure-eight')]
before=pins()
def run(case,use_old):
    kind,source=case;diagram=Diagram.from_pd(source['pd'])
    if kind=='seed':
        answer=normal_seed_decide(diagram,sector_radius=0 if use_old else 2,max_work=None)
        assert answer['status']=='UNKNOT'and verify_normal_seed_certificate(diagram,answer['certificate'])
        wire=seeds.encode(answer)
        return dict(completed=True,status=answer['status'],result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire))
    answer=recognize(diagram,**dict(seeds.FORCED,normal_seed_sector_radius=0 if use_old else 2,seconds=30))
    assert answer.status==source['expected']
    wire=seeds.encode(answer.evidence)
    return dict(completed=True,status=answer.status,method=answer.method,evidence_bytes=len(wire))
result=seeds.rounds(cases,run,15);assert before==pins()
result.update(native_source_sha256=before,scope='Longer controls for the noisy rows; complete proofs/recognition')
args.output.write_text(json.dumps(result,indent=2)+'\n')
