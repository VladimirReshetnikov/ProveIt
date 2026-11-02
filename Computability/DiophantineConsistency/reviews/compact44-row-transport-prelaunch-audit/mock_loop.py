#!/usr/bin/env python3
"""Two fake compiler/dependency steps for bounded row transport, no Lean."""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path.cwd();DRIVER=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-row-transport-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='4030748893a24268b76ee70fb97164d9b9649b796acbad1a557e73a0b9feb80a':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def run(mode):
 sp=importlib.util.spec_from_file_location('row_driver',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins=lambda:None;m.audit=lambda:{'status':'fake'}
 tmpmon=Path(tempfile.mkdtemp(prefix='row-fake-monitor-',dir='/tmp'));fake=tmpmon/'monitor.py'
 fake.write_text("from pathlib import Path\ndef monitored(cmd,env,log,timeout=600):\n"+
 " src=Path(cmd[-3]);obj=Path(cmd[-1]);obj.write_bytes(b'FAKE_ROW_OBJECT');names="+repr(m.NAMES)+"\n"+
 (" names[0]='wrong.declaration'\n" if mode=='wrong_report' else '')+
 " text=''.join(\"'\"+n+\"' depends on axioms: [propext, Classical.choice, Quot.sound]\\n\" for n in names)\n"+
 (" text+='warning: injected\\n'\n" if mode=='warning' else '')+
 (" text+='sorryAx\\n'\n" if mode=='sorry' else '')+
 " log.write_text(text);return 0,123,None\n")
 m.MONITOR=fake;calls=[]
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected process');lib,pkg=map(Path,env['LEAN_PATH'].split(':'));calls.append(1)
  deps=[str(pkg/'Init.olean'),str(lib/'DiophantineConsistency/CompactTableLookup.olean'),str(lib/'DiophantineConsistency/MFWangTiles942Core.olean')]
  if mode=='wrong_deps':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class Fake:run=staticmethod(fake_run)
 m.subprocess=Fake
 out=Path(tempfile.mkdtemp(prefix='ipra-compact-row-transport-pair-review-',dir='/tmp'));out.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(out)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();error=None
   except Exception as e:error=str(e)
  if mode=='good':need(error is None and len(calls)==2 and len(json.loads((out/'receipt.json').read_bytes())['rows'])==2,'fake loop '+str(error))
  else:
   expected={'wrong_report':'axiom report mismatch','warning':'compiler failure','sorry':'compiler failure','wrong_deps':'dependency mismatch'}[mode];need(error and expected in error,'negative '+mode+': '+str(error))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(out,ignore_errors=True);shutil.rmtree(tmpmon,ignore_errors=True)
for mode in ('good','wrong_report','warning','sorry','wrong_deps'):run(mode)
