"""Longer four-arm controls for the small kernel-reuse timing estimates."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import normal_sector as current
from normal_orbit_research import seeds
from normal_orbit_research.planar_adaptive import baseline,pins,cap_boundary,corpus_source

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
old,hashes=baseline();before=pins()
cases=[('sparse/'+name,cap_boundary(corpus_source(name)))
       for name in ('finite_trefoil_interior','finite_figureEight_interior')]
def run(raw,use_old):
    module=old['normal_sector']if use_old else current
    answer=module.sparse_disc_search(raw,max_active=1)
    assert answer['status']=='NO_VERTEX_DISC_UP_TO_SUPPORT'
    wire=seeds.encode(answer)
    return dict(completed=True,output_sha256=sha256(wire).hexdigest(),output_bytes=len(wire),
        status=answer['status'],sectors_visited=answer['sectors_visited'])
result=seeds.rounds(cases,run,15)
assert before==pins()
for row in result['cases']:
    values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
    assert all(v['completed']and v['output_sha256']==values[0]['output_sha256']for v in values)
result.update(native_source_sha256=before,native_baseline_source_sha256=hashes,
    scope='Complete bounded-support scans with internal candidate checks; no portable family exhaustion proof')
args.output.write_text(json.dumps(result,indent=2)+'\n')
