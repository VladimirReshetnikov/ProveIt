import argparse
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"fast"))
parser=argparse.ArgumentParser(description="Repeat complete size-four planar enumeration with A/A controls")
parser.add_argument("--output",type=Path,required=True)
args=parser.parse_args()
from normal_orbit_research import seeds
from normal_orbit_research.planar_sectors import baseline,pins
from fastunknot.normal_sector import enumerate_sector
from planar_sector_research.fixtures import double_capped_fibonacci,ray_digest
old,h=baseline();source=double_capped_fibonacci(4);before=pins()
def run(case,use_old):
 f=old.enumerate_sector if use_old else enumerate_sector
 rays,stats=f(source["triangulation"],source["allowed_types"])
 wire=seeds.encode(sorted(tuple(x for row in r for x in row)for r in rays))
 return dict(completed=True,output_sha256=ray_digest(rays),output_bytes=len(wire),rays=len(rays),bases=stats["bases_attempted"])
result=seeds.rounds([("enumeration/double-cap-4",None)],run,15)
assert before==pins()
values=[v for s in result["cases"][0]["samples"]+result["cases"][0]["warmups"]for v in s["measurements"].values()]
assert all(v["output_sha256"]==values[0]["output_sha256"]for v in values)
result.update(native_source_sha256=before,native_baseline_source_sha256=h,scope="Repeat noisy size-four A/A row; complete enumeration and output")
args.output.write_text(json.dumps(result,indent=2)+"\n")
