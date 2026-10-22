#!/usr/bin/env python3
"""Owned offline audits only. No received proof/build code is executed."""
import argparse,hashlib,json,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise SystemExit('Assertions must be enabled')
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args();W=a.work.resolve()
assert not W.exists() and P not in W.parents;W.mkdir(parents=True)
if (P/'MANIFEST.json').exists():
 for n,v in json.loads((P/'MANIFEST.json').read_text()).items():
  b=(P/n).read_bytes();assert len(b)==v['bytes'] and hashlib.sha256(b).hexdigest()==v['sha256'],n
for item in json.loads((P/'calculus/MANIFEST.json').read_text())['files']:
 b=(P/'calculus/upstream'/item['file']).read_bytes();assert b.endswith(b'\n');b=b[:-1];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==item['sha'],item['file']
for n,v in json.loads((P/'review/ROCQ_CURRENT_VS_RECORD.json').read_text()).items():
 b=(P/'review/current_rocq'/(n+'.v')).read_bytes();assert hashlib.sha256(b).hexdigest()==v['current']
 assert (v['current']==v['normalized91_recorded'])==v['equal']
for d in ['structural','runtime']:shutil.copytree(P/d,W/d)
for d,f in [('structural','audit_refactor.py'),('runtime','bind_ports.py'),('runtime','check_residual.py')]:
 with (W/(d+'.log')).open('w') as log:subprocess.run([sys.executable,'-B',str(W/d/f)],stdout=log,stderr=subprocess.STDOUT,check=True)
for d,f in [('structural','AUDIT.json'),('runtime','PORT_BINDING.json'),('runtime','RESIDUAL_RESULT.json')]:assert json.loads((W/d/f).read_text())==json.loads((P/d/f).read_text()),f
for f in ['PathEq.v','SourceGraphBridge.v']:assert (W/'structural/proposed'/f).read_bytes()==(P/'structural/proposed'/f).read_bytes()
r=json.loads((W/'runtime/RESIDUAL_RESULT.json').read_text());r.pop('records')
out={'status':'OWNED_SOURCE_AND_SYMBOLIC_CHECKS_PASS','kernel_compilation':'NOT PERFORMED','logical_direct_seed':'Mathematical proposal only; no executable theorem validation','runtime':r,'structural':json.loads((W/'structural/AUDIT.json').read_text())}
(W/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
