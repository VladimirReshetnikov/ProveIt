#!/usr/bin/env python3
"""Copy exact completed build evidence; never treats this copy operation as a compiler replay."""
from pathlib import Path
import argparse, gzip, hashlib, json, shutil
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
DEST=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--complete',action='store_true');args=parser.parse_args()
items=[]
def copy(src,rel):
 src=Path(src);out=DEST/rel;out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists():assert out.read_bytes()==src.read_bytes(),('Destination differs',out)
 else:shutil.copyfile(src,out)
 items.append({'source':str(src),'published':str(out.relative_to(ROOT)),'sha256':sha(out),'bytes':out.stat().st_size})
for name in ['build_serial.py','build_serial_v2.py','runner-process-group.diff','audit_serial-original-unexecuted.py','audit_serial.py','timeout-cleanup.json','inventory-initial.json','inventory-v2.json','toolchain-boundary.json','toolchain-boundary-v2.json','refresh_inventory.py']:
 copy(P/name,Path('history')/name)
for src in sorted((P/'repairs').rglob('*')):
 if src.is_file():copy(src,Path('history/repairs')/src.relative_to(P/'repairs'))
original=Path('/tmp/k215-source-partition-plan/draft1/original-KSource215.lean')
if not original.is_file():original=Path('/tmp/k215-source-partition-plan/original-KSource215.lean')
assert original.is_file()
data=gzip.compress(original.read_bytes(),mtime=0)
out=DEST/'history/KSource215-monolithic.lean.gz';out.parent.mkdir(parents=True,exist_ok=True)
if out.exists():assert out.read_bytes()==data
else:out.write_bytes(data)
items.append({'source':str(original),'published':str(out.relative_to(ROOT)),'sha256':sha(out),'uncompressed_sha256':sha(original),'bytes':len(data)})
copy(P/'test_portable_driver.py','controls/test_portable_driver.py')
for src in sorted((P/'portable-controls').iterdir()):
 if src.is_file() and src.name!='test.lock':copy(src,Path('controls')/src.name)
if args.complete:
 assert json.loads((P/'build-complete.json').read_text())['status']=='FULL_CURRENT_SOURCE_CLOSURE_PASS'
 for name in ['attempts.json','completed.json','build-complete.json','build_serial_v3.py','inventory-v3.json','toolchain-boundary-v3.json','audit_serial_v3.py','audit_serial_v4.py','portable-supervisor.py','review_final.py','review_final_v2.py','finish_after_build.py','finish_after_build_v2.py','publish_lean_evidence.py','publish_lean_evidence_v2.py','publish_lean_evidence_v3.py','build_serial_v4.py','build_serial_v5.py','inventory-v4.json','inventory-v5.json','toolchain-boundary-v4.json','toolchain-boundary-v5.json','audit_serial_v5.py','review_final_v3.py','final-review.json']:
  copy(P/name,Path('actual')/name)
 for src in sorted((P/'logs').iterdir()):copy(src,Path('actual/logs')/src.name)
 for src in sorted((P/'audit').rglob('*')):
  if src.is_file() and '.olean' not in src.name:copy(src,Path('actual/audit')/src.relative_to(P/'audit'))
# Original absolute paths remain in actual receipts; the map supplies portable publication counterparts.
mapfile=DEST/('publication-complete.json' if args.complete else 'publication-history.json')
mapfile.write_text(json.dumps({'mode':'complete' if args.complete else 'history-and-controls-only','files':items,'script_sha256':sha(Path(__file__))},indent=2)+'\n')
print(json.dumps({'files':len(items),'bytes':sum(x['bytes'] for x in items),'map':str(mapfile)},indent=2))
