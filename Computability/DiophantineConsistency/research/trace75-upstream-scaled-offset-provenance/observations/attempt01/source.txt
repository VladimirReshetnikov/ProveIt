#!/usr/bin/env python3
"""Read-only check of one named direct-import receipt; no Lean."""
from hashlib import sha256
from pathlib import Path
import json,re,sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
RECEIPT=D/'research/ten-positive-scaled-offset-generic-prototype/observations/offset-attempt01/terminal.json'
FINAL=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
TRIAGE=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout'
PINS={RECEIPT:'b65e6628a81a71aeac5481571e815c5ae5117dd09e68d3c7a4b2629251ab461e',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',
      TRIAGE:'87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
q=json.loads(RECEIPT.read_text());f=json.loads(FINAL.read_text());triage=json.loads(TRIAGE.read_text())
name='ScaledOffsetGeneric';dep='DiophantineConsistency.ArithmeticPellCongruences'
row=next(x for x in triage['records'] if x['module']==name)
need(q['exit']==0 and q['reason'] is None and q['pins']==q['after'],'producer receipt status')
need(row['exact_producer_in_six_runs'] is None and row['prior_capture']['all_companions_match'],'triage category changed')
out=Path(q['output_root'])/(name+'.olean');chosen=f['selected_project'][name]['.olean']
need(out.is_file() and str(out.resolve())==chosen['resolved'] and sha(out)==q['object_sha256']==chosen['sha256'],'output selection mismatch')
source=RECEIPT.parent/'source.txt';copy=Path(q['command'][5]);source_hash=q['pins']['source']
need(source.is_file() and copy.is_file() and sha(source)==sha(copy)==source_hash,'source copy mismatch')
imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M)
need(imports==[dep] and [x for x in f['serialized_headers'][name] if x!='Init']==imports,'source/header mismatch')
for ext in ['stdout','stderr']:
    p=RECEIPT.parent/ext;need(p.is_file() and sha(p)==q[ext+'_sha256'],'log drift '+ext)
direct=q['pins']['direct_imports'];need(set(direct)=={dep} and direct==q['after']['direct_imports'],'named direct record mismatch')
record=direct[dep];p=Path(record['path']);selected=f['selected_project'][dep]['.olean']
need(p.is_file() and str(p.resolve())==record['real_path'] and sha(p)==record['sha256']==selected['sha256'],'direct .olean mismatch')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','module':name,'producer_receipt':str(RECEIPT),
 'output_realpath':str(out.resolve()),'output_sha256':q['object_sha256'],'source_sha256':source_hash,
 'explicit_import':{'module':dep,'producer_realpath':record['real_path'],'selected_realpath':selected['resolved'],'sha256':record['sha256']},
 'scope':'one named explicit direct .olean record; implicit Init, companion/package/dynamic and transitive producer ancestry remain unauthenticated'},sort_keys=True))
