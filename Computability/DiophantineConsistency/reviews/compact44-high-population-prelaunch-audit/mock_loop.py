#!/usr/bin/env python3
"""Two fake compiler/dependency children and failure controls; no Lean."""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2];DRIVER=BASE/'research/ordinary12-ipra-bridge/compact44-high-population-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='52b10e75fe24d6aa883b7db3c011171ce7c5fc82e5c45e46ba0a39aa4aa1fd30':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def run(mode):
 sp=importlib.util.spec_from_file_location('high_driver',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 parent=json.loads((m.AUDIT/'CHECK.json').read_bytes());m.check_pins=lambda:None;m.verify_parent=lambda:parent
 mon=m.load(m.MONITOR);calls=[]
 def fake_monitored(cmd,env,log):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);calls.append(src.stem);obj.write_bytes(b'FAKE_HIGH_OBJECT')
  names=['CompactHighPopulation.model_population','CompactHighPopulation.model_lt']
  if mode=='wrong_report':names[0]='wrong.name'
  text=''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names)
  if mode=='warning':text+='warning: injected\n'
  if mode=='sorry':text+='sorryAx\n'
  log.write_text(text);return 0,123,None
 mon.monitored=fake_monitored;m.load=lambda _:mon
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected process');lib,pkg=map(Path,env['LEAN_PATH'].split(':'));deps=[str(pkg/'Init.olean'),str(lib/'DiophantineConsistency/ArithmeticMaskConstants.olean')]
  if mode=='wrong_deps':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class Fake:run=staticmethod(fake_run)
 m.subprocess=Fake
 tmp=Path(tempfile.mkdtemp(prefix='ipra-compact-high-population-pair-review-',dir='/tmp'));tmp.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(tmp)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();error=None
   except Exception as e:error=str(e)
  if mode=='good':
   need(error is None and len(calls)==2,'fake loop '+str(error));r=json.loads((tmp/'receipt.json').read_bytes());need(len(r['runs'])==2,'fake receipt')
  else:
   expected={'wrong_report':'unexpected axioms','warning':'compiler failure','sorry':'compiler failure','wrong_deps':'unexpected direct imports'}[mode];need(error is not None and expected in error,'control '+mode+': '+str(error))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(tmp,ignore_errors=True)
for mode in ('good','wrong_report','warning','sorry','wrong_deps'):run(mode)
