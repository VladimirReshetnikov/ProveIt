#!/usr/bin/env python3
"""Read-only candidate-source/log triage for 28 graph-support objects."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];R=D/'research';OVER=Path('/tmp/compact44-graph-support-join-01')
PINS={R/'trace75-upstream-141-inventory/observations/attempt01/stdout':'87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575',
      R/'trace75-upstream-19-provenance/observations/attempt01/stdout':'d9e3020b3a928aefdbc7c4601a023c6f1b40d0930d4ad4f5229d4eac36555eb3',
      R/'trace75-upstream-ten-runner-triage/observations/attempt03/stdout':'d31977de4a6c5c724f52c9b43a1caeb173a2a979a5834ab8c68b87ee4aa3a7be',
      R/'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json':'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def imports(p):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',p.read_text(),re.M)
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
inv=read(next(p for p in PINS if 'upstream-141' in str(p)));nineteen=read(next(p for p in PINS if 'upstream-19-' in str(p)));ten=read(next(p for p in PINS if 'ten-runner' in str(p)));final=read(next(p for p in PINS if 'final-assembly' in str(p)))
known={r['module'] for r in inv['records'] if r['exact_producer_in_six_runs']}|{r['module'] for r in nineteen['records']}|{r['module'] for r in ten['records']}|{'ScaledOffsetGeneric'}
workspace=list((R/'ordinary12-ipra-bridge').glob('*/*.lean'));records=[];summary=Counter();checked={}
def remember(p):
    h=sha(p);checked[str(p)]=h;return h
for x in inv['records']:
    n=x['module']
    if n in known or str(Path(x['selected_realpath']).parent)!=str(OVER/'lib/DiophantineConsistency'):continue
    short=n.split('.')[-1];chosen=final['selected_project'][n];obj=Path(chosen['.olean']['path'])
    need(obj.is_file() and str(obj.resolve())==x['selected_realpath'] and remember(obj)==x['selected_olean_sha256'],'selected object drift '+n)
    source=OVER/(short+'.lean');row={'module':n,'selected_realpath':x['selected_realpath'],'selected_olean_sha256':x['selected_olean_sha256'],
      'selected_header':x['selected_header'],'overlay_source':None,'workspace_matches':[],'overlay_logs':[],
      'local_observation_json_dual_hash_candidates':[]}
    if source.is_file():
        sh=remember(source);need(imports(source)==[i for i in x['selected_header'] if i!='Init'],'overlay source/header mismatch '+n)
        row['overlay_source']={'path':str(source),'sha256':sh};summary['overlay_source_present']+=1
        matches=[p for p in workspace if p.name==short+'.lean' and sha(p)==sh]
        need(len(matches)==1,'workspace source match not unique '+n)
        for p in matches:remember(p);row['workspace_matches'].append(str(p))
        summary['overlay_source_workspace_match']+=1
        for p in sorted(matches[0].parent.rglob('*.json')):
            try:raw=p.read_text()
            except (OSError,UnicodeDecodeError):continue
            if sh in raw and x['selected_olean_sha256'] in raw:
                row['local_observation_json_dual_hash_candidates'].append({'path':str(p),'sha256':remember(p),
                    'contains_exact_output_realpath':x['selected_realpath'] in raw})
    else:
        summary['overlay_source_missing']+=1
        if short=='ArithmeticPackingBlocks':
            p=D/'Lean/DiophantineConsistency/ArithmeticPackingBlocks.lean'
            need(p.is_file() and imports(p)==[i for i in x['selected_header'] if i!='Init'],'canonical candidate/header mismatch')
            row['workspace_candidate_only']={'path':str(p),'sha256':remember(p)}
    for log in sorted(OVER.glob(short+'*.log')):
        if log.is_file():row['overlay_logs'].append({'path':str(log),'sha256':remember(log)})
    if row['overlay_logs']:summary['has_overlay_log']+=1
    if row['local_observation_json_dual_hash_candidates']:summary['has_local_dual_hash_candidate']+=1
    records.append(row)
need(len(records)==28,'28-object selection changed')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
for p,h in checked.items():need(Path(p).is_file() and sha(p)==h,'observed artifact changed '+p)
print(json.dumps({'status':'PASS','summary':dict(summary),'records':records,
 'scope':'point-in-time source/header and filename/log candidate triage; no source-to-object producer linkage, historical direct-input authentication or Lean replay'},sort_keys=True))
