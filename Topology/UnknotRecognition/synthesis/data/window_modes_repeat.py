"""Longer early-positive control and complete trefoil recognition comparison."""
import argparse
from hashlib import sha256
from pathlib import Path
import json
import sys

ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.window_modes import baseline,pins,corpus

parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();old,hashes=baseline();before=pins()
sources={s['name']:s for s in corpus()}
cases=[('seed/optimized-positive',('seed',sources['optimized-positive'])),
       ('recognition/trefoil',('recognition',sources['trefoil']))]
def run(case,use_old):
    kind,source=case;d=Diagram.from_pd(source['pd'])
    if kind=='seed':
        call=old['normal_seed'].normal_seed_decide if use_old else normal_seed_decide
        r=call(d,sector_radius=2,max_work=None)
        assert r['status']=='UNKNOT'and verify_normal_seed_certificate(d,r['certificate'])
        assert r['stats'].get('sector_search')is None
        wire=seeds.encode(r)
        return dict(completed=True,status=r['status'],work=r['work'],
            result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire),
            certificate_sha256=sha256(seeds.encode(r['certificate'])).hexdigest())
    call=old['recognize'].recognize if use_old else recognize
    r=call(d,**dict(seeds.FORCED,normal_seed_sector_radius=2,seconds=30))
    assert r.status==source['expected']
    wire=seeds.encode(r.evidence)
    return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
result=seeds.rounds(cases,run,15);assert before==pins()
result.update(native_source_sha256=before,native_baseline_source_sha256=hashes,
    driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='Full early-positive native query that never enters mode projection, and full enabled trefoil recognition including complete fallback and serialized output. Repeat prompted by the noisy early-positive primary row and small measured window gains.')
args.output.write_text(json.dumps(result,indent=2)+'\n')
