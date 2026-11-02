#!/usr/bin/env python3
"""Six fake compile/deps steps and failure controls for exact low-mask replay."""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2];DRIVER=BASE/'research/ordinary12-ipra-bridge/compact44-low-population-exact-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='ff72d79a6e1a2cec2074f94d5f668048bbe3690e152dc3a86eb3bd78d65edf88':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def run(mode):
 spec=importlib.util.spec_from_file_location('low_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 check=json.loads((m.AUDIT/'CHECK.json').read_bytes());meta=json.loads((m.PARENT/'evidence/receipt.json').read_bytes());m.verify=lambda:(check,meta)
 mon=m.load(m.MONITOR);calls=[]
 def fake_monitored(cmd,env,log):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name);obj.write_bytes(('FAKE_'+name).encode())
  names={'CompactLowPopulation':['CompactLowPopulation.list_population','CompactLowPopulation.model_population'],'CompactSupportCard':['CompactSupportCard.support_card'],'CompactLowExact':['CompactLowExact.model_population']}[name]
  if mode=='wrong_report' and name=='CompactLowPopulation':names[0]='wrong.name'
  text=''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names)
  if mode=='warning' and name=='CompactLowPopulation':text+='warning: injected\n'
  if mode=='sorry' and name=='CompactLowPopulation':text+='sorryAx\n'
  log.write_text(text);return 0,123,None
 mon.monitored=fake_monitored;m.load=lambda _:mon
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected subprocess');src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'))
  imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()];deps=[str(pkg/'Init.olean')]+[str(lib/Path(*d.split('.')).with_suffix('.olean')) for d in imports]
  if mode=='wrong_deps' and src.stem=='CompactLowPopulation':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class Fake:run=staticmethod(fake_run)
 m.subprocess=Fake
 tmp=Path(tempfile.mkdtemp(prefix='ipra-compact-low-exact-pair-review-',dir='/tmp'));tmp.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(tmp)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();error=None
   except Exception as e:error=str(e)
  if mode=='good':
   need(error is None and len(calls)==6,'fake loop '+str(error));r=json.loads((tmp/'receipt.json').read_bytes());need(len(r['runs'])==2 and all(len(x['steps'])==3 for x in r['runs']),'fake receipt')
  else:
   expected={'wrong_report':'compiler failure','warning':'compiler failure','sorry':'compiler failure','wrong_deps':'direct import drift'}[mode];need(error is not None and expected in error,'control '+mode+': '+str(error))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(tmp,ignore_errors=True)
for mode in ('good','wrong_report','warning','sorry','wrong_deps'):run(mode)
