"""Run after integration, on user-supplied native triangulation/vector JSON fixtures.

Usage: python integration/audit_native.py --fast /path/ProveIt/Topology/UnknotRecognition/fast \
  --fixtures fixtures.json --output results/native_audit.json
Input JSON: [{"name":str,"triangulation":native_dict,"coordinates":[[...7...],...]}].
This is a reproducible runner, not a claim that native execution has happened.
"""
import argparse,json,sys,time,hashlib
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--fast',type=Path,required=True)
p.add_argument('--fixtures',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();root=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(root/'src'),str(a.fast),str(root/'integration')]
from native_selective_disk import selective_normal_disk,verify_selective_normal_disk
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.integer_codec import json_safe
cases=json.loads(a.fixtures.read_text());rows=[]
for item in cases:
    tri,x=item['triangulation'],item['coordinates']
    start=time.perf_counter();got=selective_normal_disk(tri,x);elapsed=time.perf_counter()-start
    baseline=normal_component_census(tri,x,mode='coordinates',record_certificate=True)
    assert baseline['status']=='COMPLETE'
    if got['status']=='COMPLETE':
        assert verify_selective_normal_disk(tri,x,got['certificate'])
        assert any(row.get('coordinates')==got['coordinates'] and row['compressing_disk']
                   for row in baseline['component_histogram'])
    else:
        assert got['status']=='NO_DISC_IN_SUPPLIED_VECTOR' and not baseline['contains_compressing_disk']
    rows.append(dict(name=item.get('name','unnamed'),seconds=elapsed,result=got))
manifest={str(f.relative_to(a.fast)):hashlib.sha256(f.read_bytes()).hexdigest()
          for f in sorted((a.fast/'fastunknot').glob('*.py'))}
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps(json_safe(dict(status='PASS',cases=rows,
          native_sha256=manifest,fixture_sha256=hashlib.sha256(a.fixtures.read_bytes()).hexdigest())),indent=2))
print('Native audit completed:',len(rows),'cases')
