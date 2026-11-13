#!/usr/bin/env python3
"""Read-only comparison of one reported source session and selected object."""
from hashlib import sha256
from pathlib import Path
import json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
P=D/'research/ordinary12-ipra-bridge/compact44-represented-orbit-word-prototype'
README=P/'README.md';SNAP=P/'evidence/ArithmeticPackingBlocks.lean'
SOURCE=D/'Lean/DiophantineConsistency/ArithmeticPackingBlocks.lean'
LOG=P/'observations/ArithmeticPackingBlocks-attempt01.log'
OVERLOG=Path('/tmp/compact44-graph-support-join-01/ArithmeticPackingBlocks-attempt01.log')
TRIAGE=D/'research/trace75-graph-support-28-triage/observations/attempt01/stdout'
FINAL=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
PINS={README:'958f442325b0a53dbca694ecee6091aa65896c0f5283fe5ef7ecb6d80608f950',
      SNAP:'ec2f8f5be48aee4056a69e4d804c09e7065bc5b28d780ef65ea66ecd89b77679',
      SOURCE:'ec2f8f5be48aee4056a69e4d804c09e7065bc5b28d780ef65ea66ecd89b77679',
      LOG:'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
      OVERLOG:'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
      TRIAGE:'a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
text=README.read_text();need('session 12394' in text and 'actually exited 0 with an empty log' in text and PINS[SNAP] in text,'reported session text changed')
need(SOURCE.read_bytes()==SNAP.read_bytes() and not LOG.read_bytes() and not OVERLOG.read_bytes(),'source/log comparison failed')
t=json.loads(TRIAGE.read_text());f=json.loads(FINAL.read_text());name='DiophantineConsistency.ArithmeticPackingBlocks'
row=next(x for x in t['records'] if x['module']==name);need(row['overlay_source'] is None,'overlay source no longer missing')
selected=f['selected_project'][name]['.olean'];p=Path(selected['path'])
need(p.is_file() and str(p.resolve())==selected['resolved']==row['selected_realpath'] and sha(p)==selected['sha256']==row['selected_olean_sha256'],'selected object drift')
imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',SOURCE.read_text(),re.M)
need(imports==[x for x in f['serialized_headers'][name] if x!='Init'],'source/header mismatch')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','reported_session':12394,'reported_session_exit':0,'reported_source_sha256':PINS[SNAP],
 'retained_log_sha256':PINS[LOG],'selected_object_realpath':selected['resolved'],'selected_object_sha256':selected['sha256'],
 'scope':'reported source/session and separate selected-object observation; no atomic linkage, direct-import provenance or Lean replay'},sort_keys=True))
