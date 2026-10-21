#!/usr/bin/env python3
"""Portable outer-verifier controls; source release is never modified."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
 raise SystemExit('Run without -O/-OO and unset PYTHONOPTIMIZE')
D=Path(__file__).resolve().parent.parent
def demand(p,m):
 if not p:raise RuntimeError(m)
env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
results=[]
with tempfile.TemporaryDirectory(prefix='release-outer-negative-')as td:
 W=Path(td)/'release';shutil.copytree(D,W)
 def run(flags=(),addenv=None):
  r=subprocess.run([sys.executable,*flags,str(W/'verify_release.py'),'--hash-only'],cwd=td,env=dict(env,**(addenv or {})),text=True,capture_output=True)
  return r
 r=run();demand(r.returncode==0,'relocated baseline failed');results.append({'case':'relocated_hash_only','passed':True})
 for flag in ('-O','-OO'):
  r=run([flag]);demand(r.returncode!=0 and 'UNSAFE_PYTHON_OPTIMIZATION' in r.stderr,'accepted '+flag);results.append({'case':flag,'rejected':True})
 for val in ('0','1','2'):
  r=run(addenv={'PYTHONOPTIMIZE':val});demand(r.returncode!=0 and 'UNSAFE_PYTHON_OPTIMIZATION' in r.stderr,'accepted env '+val);results.append({'case':'PYTHONOPTIMIZE='+val,'rejected':True})
 for name,old,new,diag in [
 ('rocq/snapshot/rocq/rocq-extension/coq/215/Cert215Offsets.v',b'0%Z',b'1%Z','PAYLOAD_SHA256_MISMATCH'),
 ('rocq/prototype.py',b'#!/usr/bin/env python3',b'#!/usr/bin/env pythonX','PAYLOAD_SHA256_MISMATCH'),
 ('MANIFEST.json',b'proof-simplification-release-sha256-v1',b'proof-simplification-release-sha256-v2','MANIFEST_SHA256_MISMATCH')]:
  p=W/name;raw=p.read_bytes();demand(old in raw,'mutation missing');p.write_bytes(raw.replace(old,new,1));r=run();demand(r.returncode!=0 and diag in r.stderr and 'PASS 'not in r.stderr,'mutation accepted '+name);p.write_bytes(raw);results.append({'case':'changed '+name,'rejected_before_replay':True})
 p=W/'unlisted.txt';p.write_text('unexpected file');r=run();demand(r.returncode!=0 and 'UNMANIFESTED_OR_MISSING_FILE' in r.stderr,'unlisted accepted');p.unlink();results.append({'case':'unlisted_file','rejected':True})
 r=run();demand(r.returncode==0,'restoration failed');results.append({'case':'restored_hash_only','passed':True})
print(json.dumps({'status':'PASS_OUTER_VERIFIER_NEGATIVE_CONTROLS','cases':results,'case_count':len(results),'source_release_mutated':False,'incoming_code_executed':False},indent=2))
