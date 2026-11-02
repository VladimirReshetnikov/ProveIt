#!/usr/bin/env python3
"""Isolated zero-module invalid-input control of the historical builder."""
import hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BUILDER=ROOT/'Computability/DiophantineConsistency/research/fresh-project-closure/rebuild.py'
assert subprocess.check_output(['git','show','49377c7490:'+str(BUILDER.relative_to(ROOT))],cwd=ROOT)==BUILDER.read_bytes()
with tempfile.TemporaryDirectory(prefix='ipra-builder-optimized-review-') as td:
 t=Path(td);snap=t/'snapshot';snap.mkdir();(snap/'manifest.json').write_text(json.dumps({'status':'INVALID','root':str(t),'order':[],'sources':{},'project_modules':0,'target':'not-present'}));provider=t/'provider.json';provider.write_text(json.dumps({'root':str(t/'nonexistent-foundation'),'overlay':str(t/'empty-overlay'),'manifest_sha256':'invalid','status':'INVALID','exit_code':99,'declared_external_guard':{},'foundation_artifacts':{}}));fi=t/'foundation.json';fi.write_text(json.dumps({'lean_sha256':'invalid'}))
 def run(label,optimized):
  out=t/label;env=os.environ.copy()
  if optimized:env['PYTHONOPTIMIZE']='1'
  else:env.pop('PYTHONOPTIMIZE',None)
  cmd=[sys.executable,str(BUILDER),'--snapshot',str(snap),'--output',str(out),'--provider-receipt',str(provider),'--snapshot-sha256','invalid','--provider-sha256','invalid','--foundation-input',str(fi),'--expected-axiom-reports','0']
  p=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=30);return out,p
 normal,p=run('normal',False);assert p.returncode!=0 and not normal.exists()
 optimized,q=run('optimized',True);state=json.loads((optimized/'state.json').read_text());assert q.returncode==0 and state['status']=='PASS' and state['records']==[]
r={'status':'PASS_INDEPENDENT_OPTIMIZED_BUILDER_NEGATIVE_CONTROL','builder_sha256':hashlib.sha256(BUILDER.read_bytes()).hexdigest(),'normal_invalid_fixture_exit_nonzero':True,'optimized_invalid_fixture_exit_code':0,'optimized_invalid_fixture_state':'PASS','optimized_invalid_fixture_compiled_modules':0,'scope':'Fake zero-module snapshot and fake provider; no Lean process, real provider mutation or project build.'};out=HERE/'optimized-builder-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['status'],hashlib.sha256(out.read_bytes()).hexdigest())
