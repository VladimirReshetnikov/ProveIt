#!/usr/bin/env python3
"""Owned offline replay; does not execute received source or build scripts."""
import argparse,hashlib,json,shutil,subprocess,sys,tarfile
from pathlib import Path
if not __debug__:raise SystemExit('Assertions must be enabled')
P=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args();W=a.work.resolve()
assert not W.exists() and P not in W.parents;W.mkdir(parents=True)
H=lambda b:hashlib.sha256(b).hexdigest()
if (P/'MANIFEST.json').exists():
 for n,v in json.loads((P/'MANIFEST.json').read_text()).items():
  b=(P/n).read_bytes();assert len(b)==v['bytes'] and H(b)==v['sha256'],n
R=P/'review';B=R/'current';V=B/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12'
j=json.loads((V/'integration/current-review.json').read_text());sources=[]
for k,r in j['sources'].items():
 p=r['current'].split('/Proofs/')[1];assert H((B/p).read_bytes())==r['sha256'],k;sources.append(k)
ix=json.loads((V/'lean/index.json').read_text())
with tarfile.open(V/'lean/execution.tar.gz') as t:
 for n,r in ix.items():
  f=t.extractfile(n);assert f is not None;b=f.read();assert H(b)==r['sha256'] and len(b)==r['bytes'],n
assert len(sources)==199 and len(ix)==167
for d in ['calculus','structural','runtime']:shutil.copytree(P/d,W/d)
for d,f in [('calculus','audit_forks.py'),('calculus','audit_imports.py'),('structural','build_proposal.py'),('runtime','check_templates.py'),('runtime','test_boundaries.py')]:
 with (W/(d+'_'+f+'.log')).open('w')as log:subprocess.run([sys.executable,'-B',str(W/d/f)],stdout=log,stderr=subprocess.STDOUT,check=True)
for d,n in [('calculus','AUDIT.json'),('calculus','IMPORT_AUDIT.json'),('structural','AUDIT.json'),('runtime','TEMPLATES.json'),('runtime','BOUNDARY_TESTS.json')]:assert json.loads((W/d/n).read_text())==json.loads((P/d/n).read_text()),n
for n in ['RMBisim.lean','RMNormalizedBisim.lean']:assert(W/'structural/proposed'/n).read_bytes()==(P/'structural/proposed'/n).read_bytes()
o={'status':'OWNED_STATIC_AND_SYMBOLIC_AUDITS_PASS','kernel_compilation':'NOT PERFORMED','current_sources_bound':len(sources),'archive_members_bound':len(ix),'gross_fork_inventory_not_net_deletion':805,'micro_patch_modules_removed':0,'entry_patch_net_lines_removed':6,'runtime':'Conditional opaque-prefix symbolic audit; new universal semantics uncompiled; 6176 cheap coverage instances still required.'}
(W/'verification.json').write_text(json.dumps(o,indent=2)+'\n');print(o['status'])
