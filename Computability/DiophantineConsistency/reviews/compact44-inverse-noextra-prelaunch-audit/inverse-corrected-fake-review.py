#!/usr/bin/env python3
import contextlib,hashlib,importlib.util,io,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];B=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge'
CASES=[('compact44-inverse-lookup-prototype','ec9888b8345faa873f6d419bbcedf5696f06e1f8e5ffc6ad3833353bafcac0e3','ipra-compact-inverse-lookup-pair-',['CompactRowComplete'])]
for directory,want,prefix,deplist in CASES:
 D=B/directory/'replay.py';assert hashlib.sha256(D.read_bytes()).hexdigest()==want
 for mode in ('good','wrong_report','wrong_axiom','warning','sorry','wrong_deps','compiler_exit','stop_reason','sibling_mismatch','parent_drift','missing_required'):
  sp=importlib.util.spec_from_file_location('driver',D);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins=lambda:None;calls=[];audits=[]
  def fake_audit():
   audits.append(1);return {'status':'changed'} if mode=='parent_drift' and len(audits)>1 else {'status':'fake'}
  m.audit=fake_audit
  def overlay(src,dest):
   d=dest/'DiophantineConsistency';d.mkdir(parents=True)
   for x in deplist:
    srcfile=src/'DiophantineConsistency'/f'{x}.olean';assert srcfile.is_file();(d/f'{x}.olean').symlink_to(srcfile)
  m.overlay=overlay
  tmp=Path(tempfile.mkdtemp(prefix='word-fake-monitor-',dir='/tmp'));mon=tmp/'monitor.py'
  mon.write_text("from pathlib import Path\ndef monitored(cmd,env,log,timeout=600):\n"+
   " obj=Path(cmd[-1]);obj.write_bytes("+("b'PEER_DIFFERENT' if 'peer' in str(obj) else b'OBJ'" if mode=='sibling_mismatch' else "b'OBJ'")+")\n names="+repr(m.NAMES)+"\n"+
   (" names[0]='wrong.declaration'\n" if mode=='wrong_report' else '')+
   " text=''.join(\"'\"+n+\"' depends on axioms: [\"+(\"propext\" if "+str(mode=='wrong_axiom')+" else \"propext, Classical.choice, Quot.sound\")+\"]\\n\" for n in names)\n"+
   (" text+='warning: injected\\n'\n" if mode=='warning' else '')+
   (" text+='sorryAx\\n'\n" if mode=='sorry' else '')+
   " log.write_text(text);return "+('1' if mode=='compiler_exit' else '0')+",123,"+("'injected stop'" if mode=='stop_reason' else 'None')+"\n")
  m.MONITOR=mon
  def fake_run(cmd,env=None,**kw):
   assert '--deps' in cmd;lib,pkg=map(Path,env['LEAN_PATH'].split(':'));calls.append(1);deps=[str(pkg/'Init.olean')]+[str(lib/'DiophantineConsistency'/f'{x}.olean') for x in deplist]
   if mode=='missing_required':(lib/'DiophantineConsistency/CompactRowComplete.olean').unlink()
   if mode=='wrong_deps':deps.append('/tmp/unexpected.olean')
   return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
  m.subprocess=type('Fake',(),{'run':staticmethod(fake_run)})
  out=Path(tempfile.mkdtemp(prefix=prefix+'review-',dir='/tmp'));out.rmdir();sys.argv=[str(D),'--output',str(out)]
  try:
   with contextlib.redirect_stdout(io.StringIO()):
    try:m.main();err=None
    except Exception as e:err=str(e)
   if mode=='good':assert err is None and len(calls)==2 and len(json.loads((out/'receipt.json').read_bytes())['rows'])==2,(directory,mode,err)
   else:
    expected='missing required object' if mode=='missing_required' else 'dependency mismatch' if mode=='wrong_deps' else 'axiom report mismatch' if mode in ('wrong_report','wrong_axiom') else 'paired outputs differ' if mode=='sibling_mismatch' else 'parent audit reruns differ' if mode=='parent_drift' else 'compiler failure'
    assert err and expected in err,(directory,mode,err)
   print(directory,mode,'PASS',len(calls),'fake deps')
  finally:shutil.rmtree(out,ignore_errors=True);shutil.rmtree(tmp,ignore_errors=True)
