#!/usr/bin/env python3
"""Exercise saturation driver with fake compilers/dependency queries, no Lean."""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2];DRIVER=BASE/'research/ordinary12-ipra-bridge/free-j-saturation-client-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='05e5563e0eaf17f7beb6a6e0b5412159b488c12fa615806d85b8678cef917d3f':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def trial(mode):
 spec=importlib.util.spec_from_file_location('reviewed_saturation',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 scan=json.loads((m.PLAN/'scan.json').read_bytes());review=json.loads((m.AUDIT/'CHECK.json').read_bytes());m.verify=lambda:(scan,review)
 real_load=m.load;mon=real_load(m.MONITOR);policy=real_load(m.WARNING_POLICY);calls=[]
 def fake_monitored(cmd,env,log):
  src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name);obj.write_bytes(('FAKE_'+name).encode())
  if name=='ArithmeticBinaryCarry':
   text=(f"{src}:153:12: warning: try 'simp' instead of 'simpa'\n\nNote: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
     f"{src}:159:16: warning: try 'simp' instead of 'simpa'\n\nNote: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
     f"{src}:153:54: warning: 'simp' tactic does nothing\n\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n"
     f"{src}:153:54: warning: this tactic is never executed\n\nNote: This linter can be disabled with `set_option linter.unreachableTactic false`\n")
   if mode=='missing_warning':text=''
   if mode=='changed_warning':text=text.replace(':153:12:',':153:13:')
   if mode=='extra_warning':text+='warning: injected\n'
  elif name=='FreeJSaturationClient':
   report='wrong.declaration' if mode=='wrong_report' else 'FreeJSaturationClient.graph_saturation'
   text="'"+report+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
  else:text=''
  log.write_text(text);return 0,123,None
 mon.monitored=fake_monitored;m.load=lambda path:mon if path==m.MONITOR else policy
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected subprocess');src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'))
  imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  if mode=='missing_project' and src.stem=='FreeJSaturationClient':(lib/'DiophantineConsistency/ArithmeticMaskPopulation.olean').unlink()
  deps=[str(pkg/'Init.olean')]
  for dep in imports:
   rel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/rel
   if not candidate.is_file():candidate=pkg/rel
   deps.append(str(candidate))
  if mode=='wrong_deps' and src.stem=='ArithmeticBinaryCarry':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class Fake:run=staticmethod(fake_run)
 m.subprocess=Fake
 tmp=Path(tempfile.mkdtemp(prefix='ipra-freej-saturation-client-pair-review-',dir='/tmp'));tmp.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(tmp)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='good':
   need(err is None and len(calls)==10,'full fake loop '+str(err));rec=json.loads((tmp/'receipt.json').read_bytes());need(len(rec['runs'])==2 and all(len(x['steps'])==5 for x in rec['runs']),'fake receipt')
  else:
   expected={'missing_warning':'compiler failure','changed_warning':'compiler failure','extra_warning':'compiler failure','wrong_report':'unexpected axiom report','missing_project':'project import absent from same-side overlay','wrong_deps':'direct imports differ'}[mode]
   need(err is not None and expected in err,'negative '+mode+': '+str(err))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(tmp,ignore_errors=True)
for mode in ('good','missing_warning','changed_warning','extra_warning','wrong_report','missing_project','wrong_deps'):trial(mode)
