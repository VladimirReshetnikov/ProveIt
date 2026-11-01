#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent;V=D.parent;h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();paths=[D/'prepare.py',D/'replay.py',Path(__file__)];before={str(p):h(p) for p in paths};log=D/'run.log'
with log.open('w') as f:r=subprocess.run([sys.executable,str(D/'prepare.py')],stdout=f,stderr=subprocess.STDOUT)
after={str(p):h(p) for p in paths};result={'status':'FAIL','exit_code':r.returncode,'before':before,'after':after,'log_sha256':h(log)}
if r.returncode==0 and before==after:
 a=V/'ipra-current-native14-fixed-replay';b=V/'ipra-current-native14-fixed-replay-prepare-peer';result.update(author_manifest_sha256=h(a/'manifest.json'),peer_manifest_sha256=h(b/'manifest.json'),author_replay_sha256=h(a/'replay.py'),peer_replay_sha256=h(b/'replay.py'))
 if result['author_manifest_sha256']==result['peer_manifest_sha256'] and result['author_replay_sha256']==result['peer_replay_sha256']:result['status']='PASS'
(D/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(result['status'],flush=True)
if result['status']!='PASS':raise SystemExit(1)
