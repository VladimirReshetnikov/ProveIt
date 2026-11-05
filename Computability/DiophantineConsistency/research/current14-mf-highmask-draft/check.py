#!/usr/bin/env python3
"""One guarded high-mask draft check over the authenticated base only."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];ROOT=HERE.parents[3]
COORD=TASK/'research/current14-printed-port-extension-coordinator-v3/coordinator.py'
OWNED=TASK/'research/current14-structured-endpoint-coherent-runner-v3/owned.py'
BASE_AUDIT=TASK/'reviews/current14-fresh-base-independent/receipt.json'
SOURCE=HERE/'HighMaskRecipeMF.lean';OUT=Path('/tmp/current14-mf-highmask-check-20261104')
PINS={COORD:'83dfc99170172bb241936e96f7466cd292a0e523a1e01a4e0e1cc4406fae2a1e',
      OWNED:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498',
      SOURCE:'a0434b2588508f765366ef7a1c7ff0d5bf1e43b6fb0b1c03af48e854dfe94c74'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def pin():
 for p,h in PINS.items():need(p.is_file() and sha(p)==h,('pin mismatch',str(p)))
need(not OUT.exists(),'refusing existing output');pin();c=load('mf_highmask_coord',COORD);ctx=c.context();d=c.driver
need(c.idle_lean(),'Lean slot occupied')
audit=json.loads(BASE_AUDIT.read_text());need(audit['status']=='PASS_SINGLE_SOURCE_CURRENT_ARTIFACT_AUDIT' and
    audit['base_state_sha256']==sha(d.BASE_STATE) and audit['watchdog_sha256']==sha(d.WATCHDOG),'base audit mismatch')
owned=load('mf_highmask_owned',OWNED);initial=c.final_hashes();checksha=sha(__file__);ownedsha=sha(OWNED);auditsha=sha(BASE_AUDIT)
OUT.mkdir();src=OUT/'src';src.mkdir();logs=OUT/'logs';logs.mkdir();lib=OUT/'lib';lib.mkdir();source=src/SOURCE.name;source.write_bytes(SOURCE.read_bytes());need(sha(source)==PINS[SOURCE],'staged source mismatch')
state={'status':'RUNNING','check_sha256':checksha,'source_sha256':PINS[SOURCE],'owned_sha256':ownedsha,'base_audit_sha256':auditsha,
       'initial':initial,'scope':'One high-mask draft checked against single authenticated base; no endpoint join or independent Lean replay.'}
def save():
 tmp=OUT/'state.tmp';tmp.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');tmp.replace(OUT/'state.json')
save()
env=dict(os.environ,LEAN_PATH=str(d.BASE_DIR/'lib')+':'+str(d.PKG),LEAN_NUM_THREADS='1')
for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(var,None)
def run(cmd,label,out,err):
 samples=[];start=time.monotonic()
 def check(pid):
  rss=0
  for member in owned.group_live(pid):
   try:rss+=int(Path('/proc',str(member),'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
   except FileNotFoundError:pass
  sample={'seconds':round(time.monotonic()-start,2),'session_rss_bytes':rss,'memavailable_bytes':c.available(),'free_bytes':shutil.disk_usage('/tmp').free}
  samples.append(sample);state.update(phase=label,samples=samples);save()
  return rss<5*1024**3 and sample['memavailable_bytes']>=10*1024**3 and sample['free_bytes']>=4_000_000_000
 with out.open('x') as stdout,err.open('x') as stderr:
  code,seconds,receipt=owned.run(['ionice','-c3','nice','-n19',*cmd],cwd=src,env=env,stdout=stdout,stderr=stderr,
                                 timeout=180,disk_check=check,poll_interval=1)
 need(samples,'missing resource sample');return code,seconds,receipt,samples
try:
 deps=logs/'deps.stdout';depserr=logs/'deps.stderr';code,seconds,receipt,samples=run([str(d.LEAN),'--deps',str(source)],'deps',deps,depserr)
 state['deps']={'exit':code,'seconds':seconds,'receipt':receipt,'samples':samples,'stdout_sha256':sha(deps),'stderr_sha256':sha(depserr)};save()
 need(code==0 and not depserr.read_text(),'deps command failed')
 lines=deps.read_text().splitlines();direct={};counts={}
 for line in lines:
  path=Path(line);need(path.is_absolute() and path.is_file(),'invalid dependency')
  if path.is_relative_to(d.BASE_DIR/'lib'):
   module=d.logical_name(path,d.BASE_DIR/'lib');need(module in ctx['manifest']['sources'],'unexpected project import');guard=ctx['base']['outputs'][module]
  elif path.is_relative_to(d.PKG) or path.is_relative_to(d.TOOL):
   root=d.PKG if path.is_relative_to(d.PKG) else d.TOOL;module=d.logical_name(path,root);guard={k:ctx['external_guard'][k] for k in d.scan(Path(str(path)[:-6]))}
  else:raise ValueError(('unexpected dependency root',line))
  if d.duplicate(direct,counts,module,path):continue
  observed=d.capture_input(path,sha(path));need(observed==guard,('input producer mismatch',module));direct[module]={'path':str(path),'sha256':observed[str(path)]['sha256']}
 d.validate_dependencies(lines,direct);need(set(direct)=={'Init','DiophantineConsistency.ArithmeticMaskData','DiophantineConsistency.MFPaper1982Digits'},'wrong direct imports')
 state['direct_inputs']=direct;save()
 log=logs/'lean.stdout';err=logs/'lean.stderr';obj=lib/'HighMaskRecipeMF.olean';cmd=[str(d.LEAN),'-M4000','-j1','-DElab.async=false','--root='+str(src),str(source),'-o',str(obj)]
 code,seconds,receipt,samples=run(cmd,'compile',log,err);text=log.read_text()+'\n'+err.read_text()
 state['compile']={'exit':code,'seconds':seconds,'receipt':receipt,'samples':samples,'stdout_sha256':sha(log),'stderr_sha256':sha(err),'object_sha256':sha(obj) if obj.is_file() else None};save()
 need(code==0 and obj.is_file() and not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'Lean draft failed')
 reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
 expected=['DiophantineConsistency.Current14HighMaskMF.highPort_nat_recipe','DiophantineConsistency.Current14HighMaskMF.highPort_int_recipe']
 need([n for n,_ in reports]==expected and all(not ({x.strip() for x in a.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}) for _,a in reports),'axiom reports mismatch')
 pin();c.context();need(c.final_hashes()==initial and sha(BASE_AUDIT)==auditsha and sha(source)==PINS[SOURCE] and sha(__file__)==checksha and sha(OWNED)==ownedsha,'final input drift')
 state.update(status='PASS',phase='complete',axiom_reports=reports,samples=[]);save();print('PASS high-mask draft',flush=True)
except BaseException as exc:
 state.update(status='FAILED',failure=repr(exc));save();print('FAILED',repr(exc),file=sys.stderr,flush=True);raise
