#!/usr/bin/env python3
"""26 fake compile/dependency children and guard failures, no Lean."""
import contextlib,hashlib,importlib.util,io,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path.cwd();BASE=ROOT/'Computability/DiophantineConsistency';DRIVER=BASE/'research/ordinary12-ipra-bridge/free-j-concrete-digits-client-prototype/replay.py';EXPECTED='9b760773ff4a03a67226406868ecc3de17902154c9515da20e502024f408a6bf'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!=EXPECTED:raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def run(mode):
 sp=importlib.util.spec_from_file_location('digits_driver',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 scan=json.loads((m.PLAN/'scan.json').read_bytes());review=json.loads((m.AUDIT/'CHECK.json').read_bytes());m.verify=lambda:(scan,review);mon=m.load(m.MONITOR);calls=[]
 def fake_monitored(cmd,env,log):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name);obj.write_bytes(('FAKE_'+name).encode())
  names=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M)
  if mode=='wrong_report' and name=='CompactListMask':names[0]='wrong.name'
  text=''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names)
  if mode=='warning' and name=='ArithmeticStandardCasts':text+='warning: injected\n'
  if mode=='sorry' and name=='ArithmeticStandardCasts':text+='sorryAx\n'
  log.write_text(text);return 0,123,None
 mon.monitored=fake_monitored;m.load=lambda _:mon
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected subprocess');src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'))
  imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  if mode=='missing_project' and src.stem=='FreeJConcreteDigitsClient':(lib/'DiophantineConsistency/CompactConcreteIncrement.olean').unlink()
  deps=[str(pkg/'Init.olean')]
  for dep in imports:
   rel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/rel
   if not candidate.is_file():candidate=pkg/rel
   deps.append(str(candidate))
  if mode=='wrong_deps' and src.stem=='ArithmeticStandardCasts':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class Fake:run=staticmethod(fake_run)
 m.subprocess=Fake
 tmp=Path(tempfile.mkdtemp(prefix='ipra-freej-concrete-digits-client-pair-review-',dir='/tmp'));tmp.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(tmp)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();error=None
   except Exception as e:error=str(e)
  if mode=='good':
   need(error is None and len(calls)==26,'fake loop '+str(error));r=json.loads((tmp/'receipt.json').read_bytes());need(len(r['runs'])==2 and all(len(x['steps'])==13 for x in r['runs']),'fake receipt')
  else:
   expected={'wrong_report':'unexpected axiom report','warning':'compiler failure','sorry':'compiler failure','wrong_deps':'direct imports differ','missing_project':'project import absent from same-side overlay'}[mode];need(error is not None and expected in error,'control '+mode+': '+str(error))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(tmp,ignore_errors=True)
for mode in ('good','wrong_report','warning','sorry','wrong_deps','missing_project'):run(mode)
