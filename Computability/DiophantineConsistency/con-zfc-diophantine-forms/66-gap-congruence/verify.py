#!/usr/bin/env python3
"""Isolated replay of authored checks; all upstream code remains inert."""
from pathlib import Path
import json,hashlib,tempfile,shutil,subprocess,sys,time
R=Path(__file__).resolve().parent
def require(v,m):
 if not v:raise ValueError(m)
manifest=json.loads((R/'SHA256SUMS.json').read_text())
for n,h in manifest.items():require(hashlib.sha256((R/n).read_bytes()).hexdigest()==h,'manifest '+n)
provenance=json.loads((R/'PROVENANCE.json').read_text())
for n,item in provenance['retained_members'].items():require(hashlib.sha256((R/n).read_bytes()).hexdigest()==item['sha256'],'provenance '+n)
def gitblob(p):
 raw=p.read_bytes();return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
for name,sha in json.loads((R/'review/formal/SOURCE.json').read_text())['blobs'].items():require(gitblob(R/'review/formal'/name)==sha,'formal Git blob '+name)
for item in json.loads((R/'direct/SOURCE_PINS.json').read_text())['files']:
 require(gitblob(R/'direct/sources'/(item['name']+'.lean'))==item['sha'],'direct Git blob '+item['name'])
commands=['source/build_gap_source.py','carry/verify_certificates.py','carry/rebuild_kernels.py','carry/test_certificates.py','source_audit/independent_sources.py','nine/build_nine.py','nine/verify_nine.py','nine/check_defect_exact.py','nine_audit/independent_nine_audit.py','nine_audit/check_local_identities.py','integer/build_integer.py','integer/verify_integer.py','integer/alternative_low_cost/build_integer.py','integer/alternative_low_cost/verify_integer.py','integer_audit/independent_integer_audit.py','algebra/build_and_check.py','direct/check_stack.py','direct_audit/audit.py']
with tempfile.TemporaryDirectory(prefix='conzfc-replay-') as tmp:
 root=Path(tmp)/'release';shutil.copytree(R,root)
 ledger={}
 for name in ['nine/generated','nine/fixed','integer/generated','integer/fixed','integer/alternative_low_cost/generated','integer/alternative_low_cost/fixed']:
  for p in (root/name).rglob('*'):
   if not p.is_file():continue
   ledger[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
 for command in commands:
  start=time.monotonic();r=subprocess.run([sys.executable,str(root/command)],cwd=root,capture_output=True,text=True)
  if r.returncode:print(r.stdout,r.stderr);raise RuntimeError(command)
  print('PASS',command,round(time.monotonic()-start,2),'s',flush=True)
 for n,h in ledger.items():require(hashlib.sha256((root/n).read_bytes()).hexdigest()==h,'rebuild '+n)
 print('PASS',len(manifest),'file hashes;',len(provenance['retained_members']),'retained source matches;',len(ledger),'byte-exact generated rebuilds')
