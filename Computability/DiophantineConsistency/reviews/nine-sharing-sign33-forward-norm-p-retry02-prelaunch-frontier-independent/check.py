#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-retry02';old=d/'research/nine-sharing-sign33-forward-norm-p-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
n='Sign33ForwardNormP';new=(p/'src/DiophantineConsistency'/f'{n}.lean').read_text();prev=(old/'src/DiophantineConsistency'/f'{n}.lean').read_text();assert sha(p/'src/DiophantineConsistency'/f'{n}.lean')=='53ca289ae6f0dc79b03cc5072bd3b45bcc57f561988afefe991209bf7f710c3f' and sha(old/'src/DiophantineConsistency'/f'{n}.lean')=='fccbcedbe2384a7957070704048ccc9f19dff2a414ac42a9c5329956e2a78166'
before='  have ht : ι (v 27) = d.tau := by\n    simpa [v, SharingForward33.witnessCoordinates] using htau';after='  have hv27 : v 27 = tau := by\n    simp [v, SharingForward33.witnessCoordinates]\n  have ht : ι (v 27) = d.tau := by\n    rw [hv27]\n    exact htau';assert prev.count(before)==1 and prev.replace(before,after)==new
assert sha(old/'attempt01/state.json')=='99e21c0f27a5640f0968a60b9f6e86dd8818413f5af0c90f77a0bc578401c4e3'
assert sha(p/'source-manifest.json')=='9f1f397903f1b1f773873387b64bfa4391b4ba1298a04dc6ca55c9fa3860d073' and sha(p/'run.py')=='52b4371c30212c72766e3f7dec1c7f313d3dbc0d24230d8dfda08477d648e48e'
a=(old/'run.py').read_text().replace('nine-sharing-sign33-forward-norm-p-retry01-20261106','nine-sharing-sign33-forward-norm-p-retry02-20261106').replace('f7160b82b506b271f9911b87bdfc624eeadbba8aa14241d55ce54a4cbb3bd59b','9f1f397903f1b1f773873387b64bfa4391b4ba1298a04dc6ca55c9fa3860d073');assert a==(p/'run.py').read_text()
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'targeted proof retry; no Lean replay'},indent=2,sort_keys=True))
