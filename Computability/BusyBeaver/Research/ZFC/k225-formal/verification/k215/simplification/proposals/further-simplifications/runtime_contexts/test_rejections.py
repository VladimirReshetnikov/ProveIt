#!/usr/bin/env python3
"""Owned optimized-mode and modified-input rejection controls, using temporary copies."""
from pathlib import Path
import json,os,shutil,subprocess,sys,tempfile
if not __debug__:raise SystemExit('Assertions must be enabled')
ROOT=Path(__file__).resolve().parent

def main():
 checks={}
 for f in ['factor_decoder.py','profile_home.py','verify_home.py']:
  for mode in ['-O','-OO','environment']:
   cmd=[sys.executable]+([]if mode=='environment'else[mode])+[str(ROOT/f)]
   env=os.environ.copy()
   if mode=='environment':env['PYTHONOPTIMIZE']='1'
   out=subprocess.run(cmd,capture_output=True,text=True,env=env,timeout=20)
   assert out.returncode!=0 and 'Assertions must be enabled'in(out.stdout+out.stderr),(f,mode,out.stdout,out.stderr)
   checks[f+':'+mode]='rejected'
 with tempfile.TemporaryDirectory(prefix='k215-pin-negative-')as td:
  work=Path(td)/'x';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__'))
  p=work/'inputs'/'KTable215.lean';p.write_bytes(p.read_bytes()+b'\n')
  out=subprocess.run([sys.executable,'-I','-B',str(work/'factor_decoder.py')],capture_output=True,text=True,timeout=20)
  assert out.returncode!=0 and'Pinned input changed: KTable215.lean'in(out.stdout+out.stderr)
  checks['changed_pinned_table']='rejected'
 (ROOT/'rejection_controls.json').write_text(json.dumps(checks,indent=2)+'\n')
 print(json.dumps(checks,indent=2))
if __name__=='__main__':main()
