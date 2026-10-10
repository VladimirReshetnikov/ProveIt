"""Repeat the noisy complete genus-one native query with four paired arms."""
import argparse
from hashlib import sha256
from pathlib import Path
import json
import sys

ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.window_euler import baseline,pins,corpus

parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();old,hashes=baseline();before=pins()
source=next(s for s in corpus()if s['name']=='genus-one-miss')
def run(case,use_old):
    d=Diagram.from_pd(source['pd'])
    call=old['normal_seed'].normal_seed_decide if use_old else normal_seed_decide
    r=call(d,sector_radius=2,max_work=None)
    assert r['status']=='UNKNOT'and verify_normal_seed_certificate(d,r['certificate'])
    wire=seeds.encode(r)
    return dict(completed=True,status=r['status'],work=r['work'],
        result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire),
        certificate_sha256=sha256(seeds.encode(r['certificate'])).hexdigest())
result=seeds.rounds([('seed/genus-one-miss',source)],run,15);assert before==pins()
result.update(native_source_sha256=before,native_baseline_source_sha256=hashes,
    driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='Full native radius-two query, independent positive replay and serialization; repeat prompted by the new-arm A/A ratio of 1.067 in the primary run')
args.output.write_text(json.dumps(result,indent=2)+'\n')
