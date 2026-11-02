#!/usr/bin/env python3
"""Fake both low-even children and exercise failure controls, no Lean."""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile,types
from pathlib import Path
D=Path(__file__).resolve().parents[2]/'research/ordinary12-ipra-bridge/compact44-low-even-prototype/replay.py'
spec=importlib.util.spec_from_file_location('driver',D);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert hashlib.sha256(D.read_bytes()).hexdigest()=='12f9f6d08e5c94f461f0d12770789594f4844f82a0b23c808340e896e2f14890'
audit=json.loads((m.AUDIT/'CHECK.json').read_bytes())
for mode in ('good','wrong_report','warning','sorry','wrong_deps','compiler_exit','seed_drift','stop_reason','sibling_mismatch','post_parent_drift'):
 calls=[];verify_calls=[]
 def fake_verify():
  verify_calls.append(1)
  return {'changed':True} if mode=='post_parent_drift' and len(verify_calls)>1 else audit
 m.verify=fake_verify
 def overlay(src,dst):
  target=dst/'DiophantineConsistency/CompactConcreteIncrement.olean';target.parent.mkdir(parents=True)
  shutil.copyfile(src/'DiophantineConsistency/CompactConcreteIncrement.olean',target)
 def monitored(cmd,env,log):
  calls.append(cmd);Path(cmd[-1]).write_bytes(b'PEER_DIFFERENT' if mode=='sibling_mismatch' and len(calls)==2 else b'FAKE_OBJECT')
  text=m.EXPECTED
  if mode=='wrong_report':text=text.replace('low_even','wrong')
  if mode=='warning':text+='warning: injected\n'
  if mode=='sorry':text+='sorryAx\n'
  if mode=='seed_drift':Path(env['LEAN_PATH'].split(':')[0]+'/DiophantineConsistency/CompactConcreteIncrement.olean').write_bytes(b'corrupt')
  log.write_text(text);return (1 if mode=='compiler_exit' else 0),123,('injected stop' if mode=='stop_reason' else None)
 class Loader:
  def exec_module(self,mod):mod.overlay=overlay;mod.monitored=monitored
 m.importlib=types.SimpleNamespace(util=types.SimpleNamespace(spec_from_file_location=lambda *_:types.SimpleNamespace(loader=Loader()),module_from_spec=lambda _:types.SimpleNamespace()))
 def fake_run(cmd,env=None,**kw):
  assert '--deps' in cmd
  lib,pkg=map(Path,env['LEAN_PATH'].split(':'));lines=[str(pkg/'Init.olean'),str(lib/'DiophantineConsistency/CompactConcreteIncrement.olean')]
  if mode=='wrong_deps':lines.append('/tmp/unexpected.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(lines)+'\n',stderr='')
 m.subprocess=types.SimpleNamespace(run=fake_run)
 out=Path(tempfile.mkdtemp(prefix='ipra-compact-low-even-pair-review-',dir='/tmp'));out.rmdir();sys.argv=[str(D),'--output',str(out)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='good':assert err is None and len(calls)==2 and len(json.loads((out/'receipt.json').read_text())['runs'])==2,(mode,err)
  else:assert err is not None and (('deps' in err) if mode=='wrong_deps' else ('sibling mismatch' in err) if mode=='sibling_mismatch' else ('audit or driver drift' in err) if mode=='post_parent_drift' else ('compiler/result mismatch' in err)),(mode,err)
  print(mode,'PASS',len(calls),'fake compiler calls')
 finally:shutil.rmtree(out,ignore_errors=True)
