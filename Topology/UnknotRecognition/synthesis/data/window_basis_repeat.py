"""Repeat the microsecond empty-recognition control without window work."""
import argparse
from pathlib import Path
import json
import sys

ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram,recognize
from normal_orbit_research import seeds
from normal_orbit_research.window_basis import baseline,pins

parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();old,hashes=baseline();before=pins();d=Diagram.from_pd([])
def run(case,use_old):
    call=old['recognize'].recognize if use_old else recognize
    r=call(d,**dict(seeds.FORCED,normal_seed_sector_radius=2,seconds=30))
    assert r.status=='UNKNOT'
    wire=seeds.encode(r.evidence)
    return dict(completed=True,status=r.status,method=r.method,evidence_bytes=len(wire))
result=seeds.rounds([('recognition/empty-circle',None)],run,31);assert before==pins()
result.update(native_source_sha256=before,native_baseline_source_sha256=hashes,
    scope='Longer microsecond early-return A/A control; no kernel-update speedup inferred')
args.output.write_text(json.dumps(result,indent=2)+'\n')
