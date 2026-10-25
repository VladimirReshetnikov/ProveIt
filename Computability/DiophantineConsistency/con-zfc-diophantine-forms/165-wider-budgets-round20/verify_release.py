#!/usr/bin/env python3
"""Authenticate the sealed inventory; execute all checks in a disposable copy."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parent

def census(root):
 return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(root.rglob('*')) if p.is_file() and p!=root/'MANIFEST_SHA256.json'}
def verify(integrity_only=False):
 expected=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())['files']
 if any(p.is_symlink() for p in ROOT.rglob('*')):raise ValueError('Symlink in release')
 if census(ROOT)!=expected:raise ValueError('Release inventory or bytes differ')
 if integrity_only:return {'status':'PASS','manifest_files':len(expected),'mode':'integrity only'}
 plan=json.loads((ROOT/'VERIFY_PLAN.json').read_text());runs=[]
 with tempfile.TemporaryDirectory(prefix='conzfc_round20_') as td:
  work=pathlib.Path(td)/'release';shutil.copytree(ROOT,work)
  env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
  for step in plan['steps']:
   cmd=[sys.executable,'-B']+step['arguments'];t=time.monotonic()
   env['PYTHONOPTIMIZE']='1' if '-O' in step['arguments'] else '0'
   result=subprocess.run(cmd,cwd=work/step.get('cwd','.'),capture_output=True,text=True,env=env)
   run={'name':step['name'],'arguments':step['arguments'],'returncode':result.returncode,'seconds':round(time.monotonic()-t,3),'stdout':result.stdout,'stderr':result.stderr};runs.append(run)
   if result.returncode:
    print(json.dumps({'status':'FAIL','runs':runs},indent=2));raise RuntimeError('Failed: '+step['name'])
 if census(ROOT)!=expected:raise ValueError('Original release modified')
 return {'status':'PASS','manifest_files':len(expected),'commands':len(runs),'runs':runs,'scope':'Finite identities and reconstruction; ordinary unbounded proofs and inherited calibration are separate. No consistency decision or new formal-kernel certificate.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path);ap.add_argument('--integrity-only',action='store_true');a=ap.parse_args()
 if a.output and a.output.resolve().is_relative_to(ROOT):raise ValueError('Receipt must be outside sealed directory')
 text=json.dumps(verify(a.integrity_only),indent=2)+'\n'
 if a.output:a.output.write_text(text)
 print(text)
