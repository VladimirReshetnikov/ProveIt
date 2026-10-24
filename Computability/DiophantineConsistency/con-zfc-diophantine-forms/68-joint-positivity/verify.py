#!/usr/bin/env python3
"""Offline isolated replay. Only authored programs run; inherited code is inert."""
from pathlib import Path
import json,hashlib,tempfile,shutil,subprocess,sys,time
R=Path(__file__).resolve().parent
def require(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((R/'SHA256SUMS.json').read_text())
for n,h in manifest.items():require(sha(R/n)==h,'manifest '+n)
prov=json.loads((R/'PROVENANCE.json').read_text())
for n,m in prov['retained_members'].items():require(sha(R/n)==m['sha256'],'provenance '+n)
for m in json.loads((R/'review/FORMAL_PINS.json').read_text()):
 p=R/'review/formal'/m['name'];raw=p.read_bytes()
 require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==m['sha'],'formal Git blob '+m['name'])
commands=[['integer_system/build_pair_guard.py'],['integer_system_audit/independent_check.py'],['-O','integer_system_audit/independent_check.py'],['report/check_displayed_rows.py'],['packing/verify.py'],['packing/audit.py'],['-O','packing/audit.py'],['alternative/build_branch_scratch.py'],['alternative/independent_scratch.py'],['alternative/independent_scratch.py','--output-wires'],['alternative/independent_scratch.py','--output-wires','--horn'],['alternative/check_branch_scratch.py'],['direct/check_flow.py'],['direct/check_affine_products.py'],['direct/build_shared_affine_step.py'],['direct/emit_shared_affine_constructor.py'],['direct/check_shared_affine_step.py'],['direct_audit/check.py'],['-O','direct_audit/check.py'],['disjointness/check_direct_parity.py'],['disjointness_audit/check_independent.py'],['free_carrier_audit/check_local_lemmas.py']]
extra=R/'norm/final10/REPLAY_COMMANDS.json'
if extra.exists():
 for cmd in json.loads(extra.read_text()):
  if cmd not in commands:commands.append(cmd)
with tempfile.TemporaryDirectory(prefix='conzfc-round10-replay-') as tmp:
 root=Path(tmp)/'release';shutil.copytree(R,root)
 ledger={}
 for dirname in ['integer_system','alternative','direct','norm/final10']:
  for p in (root/dirname).rglob('*'):
   if p.is_file() and (p.suffix=='.json' and not any(x in p.name.upper() for x in ['CHECK','AUDIT','BUILD','RESULT']) or p.suffix=='.lean' or p.parent.name=='fixed'):
    if 'baseline' not in p.parts:ledger[str(p.relative_to(root))]=sha(p)
 for cmd in commands:
  ix=1 if cmd[0]=='-O' else 0; program=root/cmd[ix]
  args=cmd[:ix]+[str(program)]+[str(root/a) if (root/a).exists() else a for a in cmd[ix+1:]]
  start=time.monotonic();p=subprocess.run([sys.executable,*args],cwd=program.parent,capture_output=True,text=True)
  if p.returncode:print(p.stdout,p.stderr);raise RuntimeError(str(cmd))
  print('PASS',' '.join(cmd),round(time.monotonic()-start,2),'s',flush=True)
 for n,h in ledger.items():require(sha(root/n)==h,'byte-exact rebuild '+n)
 print('PASS',len(commands),'suites;',len(manifest),'sealed hashes;',len(prov['retained_members']),'retained members;',len(ledger),'generated-byte checks',flush=True)
