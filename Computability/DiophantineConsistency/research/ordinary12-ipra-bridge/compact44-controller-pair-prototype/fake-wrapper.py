#!/usr/bin/env python3
import contextlib,importlib.util,io,json,shutil,subprocess,sys,tempfile,types
from pathlib import Path
D=Path(__file__).resolve().parent/'replay.py'
for mode in ('good','warning_changed','missing_required','wrong_deps','compiler_error','stop_reason','peer_mismatch','source_drift','guard_drift','head_drift','missing_report','extra_axiom','extra_warning','symlink_output','missing_output','unexpected_companion','parent_drift','frozen_symlink','late_source','late_symlink'):
 sp=importlib.util.spec_from_file_location('draft',D);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);verifies=[]
 def verify(view):
  verifies.append(1)
  if len(verifies)>1 and mode in ('late_source','late_symlink'):
   src=out/'src/DiophantineConsistency/ArithmeticControllerDataCompact44.lean'
   if mode=='late_source':src.write_text(src.read_text()+'\n-- late drift\n')
   else:
    backing=src.parent/'late-backing.lean';backing.write_bytes(src.read_bytes());src.unlink();src.symlink_to(backing)
  return {'fake':'changed'} if mode=='parent_drift' and len(verifies)>1 else {'fake':'plan'}
 m.verify=verify;heads=[];calls=[]
 def head():heads.append(1);return 'wrong' if mode=='head_drift' and len(heads)>1 else 'fake-head'
 m.githead=head;mon=m.load(m.MONITOR)
 def overlay(src,dest):
  for rel in ['DiophantineConsistency/ArithmeticStandardCasts.olean','DiophantineConsistency/ArithmeticControllerLift.olean','DiophantineConsistency/ArithmeticPackingBlocks.olean','BusyBeaver/ZFC/ArithmeticCantor.olean']:
   x=dest/rel;x.parent.mkdir(parents=True,exist_ok=True);x.symlink_to(src/rel)
 mon.overlay=overlay
 def monitored(cmd,env,log,timeout=600):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name)
  if mode=='symlink_output':
   target=obj.parent/'fake-output-bytes';target.write_bytes(b'OBJ');obj.symlink_to(target)
  elif mode!='missing_output':obj.write_bytes(b'PEER_DIFF' if mode=='peer_mismatch' and 'peer' in str(obj) else ('OBJ_'+name).encode())
  idx=0 if name.endswith('DataCompact44') else 1
  text=m.observed_expected(m.OBS[idx]).replace('<SOURCE>',str(src))
  if mode=='warning_changed':text=text.replace('warning:','warning: modified ',1)
  if mode=='missing_report':text=text[:text.find("'DiophantineConsistency.")]
  if mode=='extra_axiom':text=text.replace('Quot.sound','Quot.sound, injected',1)
  if mode=='extra_warning':text+='warning: injected\n'
  if mode=='source_drift':src.write_text(src.read_text()+'\n-- drift\n')
  if mode=='frozen_symlink':
   backing=src.parent/'same-bytes-backing.lean';backing.write_bytes(src.read_bytes());src.unlink();src.symlink_to(backing)
  if mode=='guard_drift':(Path(env['LEAN_PATH'].split(':')[0])/'DiophantineConsistency/ArithmeticStandardCasts.olean').unlink()
  if mode=='unexpected_companion':(Path(env['LEAN_PATH'].split(':')[0])/'DiophantineConsistency/ArithmeticStandardCasts.ilean').write_bytes(b'injected')
  log.write_text(text);return (1 if mode=='compiler_error' else 0),123,('stop' if mode=='stop_reason' else None)
 mon.monitored=monitored;m.load=lambda _:mon
 def fake_run(cmd,env=None,**kw):
  assert '--deps' in cmd;lib,pkg=map(Path,env['LEAN_PATH'].split(':'));src=Path(cmd[-1]);data=src.stem.endswith('DataCompact44');deps=[pkg/'Init.olean']+([lib/'DiophantineConsistency/ArithmeticStandardCasts.olean',lib/'DiophantineConsistency/ArithmeticControllerLift.olean',lib/'DiophantineConsistency/ArithmeticPackingBlocks.olean',pkg/'Mathlib/Tactic/ReduceModChar.olean'] if data else [lib/'DiophantineConsistency/ArithmeticControllerDataCompact44.olean',lib/'BusyBeaver/ZFC/ArithmeticCantor.olean'])
  if mode=='wrong_deps':deps.append(Path('/tmp/unexpected.olean'))
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(map(str,deps))+'\n',stderr='')
 m.subprocess=types.SimpleNamespace(run=fake_run)
 if mode=='missing_required':
  old=mon.overlay
  def missing(src,dest):old(src,dest);(dest/'DiophantineConsistency/ArithmeticControllerLift.olean').unlink()
  mon.overlay=missing
 out=Path(tempfile.mkdtemp(prefix='ipra-compact-controller-pair-review-',dir='/tmp'));out.rmdir();sys.argv=[str(D),'--output',str(out),'--expected-head','fake-head','--historical-view','/tmp/ipra-historical-audit-review-01']
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='good':assert err is None and len(calls)==4,(mode,err)
  else:
   assert err is not None,(mode,err)
   if mode=='source_drift':assert 'source or HEAD drift' in err or 'frozen source drift' in err,(mode,err)
   if mode in ('frozen_symlink','late_source','late_symlink'):assert 'frozen source drift' in err,(mode,err)
  print(mode,'PASS',len(calls),'fake children')
 finally:shutil.rmtree(out,ignore_errors=True)
