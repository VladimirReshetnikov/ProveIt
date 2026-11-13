#!/usr/bin/env python3
import contextlib,hashlib,importlib.util,io,json,os,re,shutil,subprocess,sys,tempfile,types
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];D=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-symbolic-graph-join-prototype/replay.py';blob=subprocess.check_output(['git','show','0819ac850a:'+D.relative_to(ROOT).as_posix()],cwd=ROOT);assert hashlib.sha256(blob).hexdigest()=='bf7962748f96af3784700c3e4b602e5ec80cde8617b4128cc04658fae6fed3ff'
for key in ('PYTHONPATH','PYTHONHOME','LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT'):os.environ[key]='REVIEW_CANARY'
for mode in ('missing_init',):
 m=types.ModuleType('historical_driver');m.__file__=str(D);exec(compile(blob,str(D),'exec'),m.__dict__);scan=json.loads((m.PLAN/'scan.json').read_bytes());review=json.loads((m.AUDIT/'CHECK.json').read_bytes());low=json.loads((m.LOW_AUDIT/'CHECK.json').read_bytes());checks=[]
 def verify():
  checks.append(1);return (scan,{'changed':True},low) if mode=='parent_drift' and len(checks)>1 else (scan,review,low)
 m.verify=verify;m.PACKAGE=Path('/tmp/review-init-absent-package');assert not (m.PACKAGE/'Init.olean').exists();mon=m.load(m.MONITOR);calls=[]
 def monitored(cmd,env,log):
  assert not any(k.startswith('PYTHON') or k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT') for k in env);src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;calls.append(name);obj.write_bytes(('PEER_DIFFERENT' if mode=='sibling_mismatch' and 'peer' in str(obj) else 'FAKE_'+name).encode())
  names=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M)
  if mode=='wrong_report' and name=='CompactLowPopulation':names[0]='wrong.declaration'
  lines=[]
  for n in names:
   axs=['propext'] if n=='CompactHighResidue.natural_mod_eight' else ['propext','Classical.choice','Quot.sound']
   if name=='CompactLowPopulation' and mode=='missing_axiom':axs.pop()
   if name=='CompactLowPopulation' and mode=='extra_axiom':axs.append('extra_axiom')
   if name=='CompactHighResidue' and n.endswith('natural_mod_eight') and mode=='changed_axiom':axs.append('Classical.choice')
   lines.append("'"+n+"' depends on axioms: ["+', '.join(axs)+"]\n")
  if mode=='warning' and name=='CompactLowPopulation':lines.append('warning: injected\n')
  if mode=='sorry' and name=='CompactLowPopulation':lines.append('sorryAx\n')
  log.write_text(''.join(lines));return (1 if mode=='compiler_exit' else 0),123,('injected stop' if mode=='stop_reason' else None)
 mon.monitored=monitored;m.load=lambda _:mon
 def fake_run(cmd,env=None,**kw):
  assert '--deps' in cmd;src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'))
  imports=[x for line in src.read_text().splitlines() if line.startswith('import ') for x in line[7:].split()]
  if mode=='missing_project' and src.stem=='CompactLowEven':(lib/'DiophantineConsistency/CompactConcreteIncrement.olean').unlink()
  deps=[str(pkg/'Init.olean')]
  for dep in imports:
   rel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/rel
   if not candidate.is_file():candidate=pkg/rel
   deps.append(str(candidate))
  if mode=='wrong_deps' and src.stem=='CompactLowPopulation':deps.append('/tmp/extra.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 m.subprocess=type('Fake',(),{'run':staticmethod(fake_run)})
 out=Path(tempfile.mkdtemp(prefix='ipra-compact-symbolic-graph-join-pair-review-',dir='/tmp'));out.rmdir();sys.argv=[str(D),'--output',str(out)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode in ('good','missing_init'):assert err is None and len(calls)==14 and all(len(x['steps'])==7 for x in json.loads((out/'receipt.json').read_bytes())['runs']),(mode,err)
  else:
   expected='unexpected axiom report' if mode in ('wrong_report','missing_axiom','extra_axiom','changed_axiom') else 'direct imports differ' if mode=='wrong_deps' else 'project import absent' if mode=='missing_project' else 'paired outputs differ' if mode=='sibling_mismatch' else 'parent inputs or driver changed' if mode=='parent_drift' else 'compiler failure'
   assert err and expected in err,(mode,err)
  print('HISTORICAL_DRIVER_ACCEPTED_MISSING_INIT',len(calls),'fake compiler calls')
 finally:shutil.rmtree(out,ignore_errors=True)
