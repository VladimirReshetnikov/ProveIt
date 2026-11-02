#!/usr/bin/env python3
"""Exercise exact committed wrapper control flow with fake compiler/deps, no Lean."""
import contextlib,hashlib,importlib.util,io,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2]
DRIVER=BASE/'research/ordinary12-ipra-bridge/free-j-population-client-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest() != '793a6873afd3517b85828e54421ee16cbd6077091b08318fb6bc62611d20de8f': raise ValueError('reviewed driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def trial(mode):
 spec=importlib.util.spec_from_file_location('review_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 scan=json.loads((m.PLAN/'scan.json').read_bytes());review=json.loads((m.AUDIT/'CHECK.json').read_bytes());m.verify=lambda:(scan,review)
 mon=m.load(m.MONITOR);calls=[]
 def fake_monitored(cmd,env,log):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name)
  obj.write_bytes(('FAKE_OBJECT_'+name).encode())
  report={'FreeJPopulationFactsNarrow':'FreeJPopulationFacts.population_of_ordinary_facts','FreeJPopulationClient':'FreeJPopulationClient.graph_population'}.get(name)
  if mode=='wrong_report' and name=='FreeJPopulationFactsNarrow':report='wrong.theorem'
  log.write_text(("'"+report+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n") if report else '')
  if mode=='warning' and name=='ArithmeticPow':log.write_text('warning: injected\n')
  return 0,123,None
 mon.monitored=fake_monitored;m.load=lambda path:mon
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected subprocess');src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'))
  imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  if mode=='missing_project' and src.stem=='FreeJPopulationClient':
   target=lib/'DiophantineConsistency/FreeJPopulationFactsNarrow.olean';target.unlink()
  deps=[str(pkg/'Init.olean')]
  for dep in imports:
   rel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/rel
   if not candidate.is_file():candidate=pkg/rel
   deps.append(str(candidate))
  if mode=='wrong_deps' and src.stem=='ArithmeticPow':deps.append('/tmp/unexpected.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 # Modify only the imported wrapper's subprocess reference, not subprocess globally.
 class FakeSubprocess:
  run=staticmethod(fake_run)
 m.subprocess=FakeSubprocess
 tmp=Path(tempfile.mkdtemp(prefix='ipra-freej-population-client-pair-review-',dir='/tmp'));tmp.rmdir()
 old=sys.argv;sys.argv=[str(DRIVER),'--output',str(tmp)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();error=None
   except Exception as e:error=str(e)
  if mode=='good':
   need(error is None and len(calls)==22,'full fake loop '+str(error));r=json.loads((tmp/'receipt.json').read_bytes());need(len(r['runs'])==2 and all(len(x['steps'])==11 for x in r['runs']),'fake receipt')
  else:
   expected={'wrong_report':'unexpected axiom report','warning':'compiler failure','missing_project':'project import absent from same-side overlay','wrong_deps':'direct imports differ'}[mode]
   need(error is not None and expected in error,'negative control '+mode+': '+str(error))
  print(mode, 'PASS', 'fake_children',len(calls))
 finally:
  sys.argv=old;shutil.rmtree(tmp,ignore_errors=True)
for mode in ('good','wrong_report','warning','missing_project','wrong_deps'):trial(mode)
