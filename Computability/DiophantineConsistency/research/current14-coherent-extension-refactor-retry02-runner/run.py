#!/usr/bin/env python3
"""Guarded source-pinned 522-stage extension with eight K215 proof refactors. No Lean without --run."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,threading,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;ROOT=P.parents[3];D=ROOT/'Computability/DiophantineConsistency';R=D/'research'
BASE=Path('/tmp/current14-standard-fresh-build-20261104');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';OUT=Path('/tmp/current14-coherent490-refactor-retry02-20261110')
INSPECT=R/'current14-coherent-extension-preflight/inspect.py';AUDIT=D/'reviews/current14-coherent-extension-preflight-independent/check.py';AUDIT_RESULT=AUDIT.parent/'result.json';MON=P/'monitor.py';PLAN=P/'plan.json';CLIENT=P/'Current14CoherentAudit.lean'
PLAN_PIN='659c292bd3a54de7745c5a9173c92872932c16c4f9574de0a8d695a0d7641ebf';MON_PIN='5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0';CLIENT_PIN='b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e';INSPECT_PIN='23e1ba624220da6615bfe8046e4e82403dcd3617b5e92efc30816b70fb059a1d';AUDIT_PIN='a59fe861b7dff4ff9d644901de1de58d89e151a74b58bed388c50c8a99126ae6';AUDIT_RESULT_PIN='255a244abfa1606b2f08a87b638e864b4898416402412490a5a74550a4c82eb4';LEAN_PIN='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
DISK_FLOOR=5_100_000_000;MEM_FLOOR=10*1024**3;RSS_LIMIT=4*1024**3;CHILD_SECONDS=180;TOTAL_SECONDS=6*3600;INTERVAL=.2
SUFFIXES=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
ACTIVE_WATCH=None
AXIOMS={'propext','Classical.choice','Quot.sound'}
REPORTS=['DiophantineConsistency.Current14QuotedPrefix.quoted_translated_endpoint','DiophantineConsistency.CurrentWitnessEquivalence2011.positive_zero_iff_zfc_refutation','DiophantineConsistency.ObjectCurrentEquation2011.eval_expression']
class Refusal(RuntimeError):pass
def need(q,msg):
 if not q:raise Refusal(msg)
def sha(p,watch_resources=True):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):
   if watch_resources and ACTIVE_WATCH is not None:ACTIVE_WATCH.check()
   h.update(b)
 return h.hexdigest()
def mem_available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise Refusal('MemAvailable missing')
def decision(disk,mem,elapsed):
 if disk<=DISK_FLOOR:return 'disk_floor'
 if mem<MEM_FLOOR:return 'host_memory_floor'
 if elapsed>=TOTAL_SECONDS:return 'total_timeout'
 return None
def no_live_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):raise Refusal('another Lean process is active')
  except (FileNotFoundError,ProcessLookupError):continue
class Watch:
 def __init__(self,start):self.start=start;self.reason=None;self.done=threading.Event();self.thread=threading.Thread(target=self.loop,daemon=True)
 def loop(self):
  while not self.done.is_set():
   try:self.reason=decision(shutil.disk_usage('/tmp').free,mem_available(),time.monotonic()-self.start)
   except BaseException as e:self.reason='watchdog_error:'+repr(e)
   if self.reason:self.done.set();return
   self.done.wait(INTERVAL)
 def begin(self):self.thread.start()
 def check(self):
  if self.reason:raise Refusal(self.reason)
  why=decision(shutil.disk_usage('/tmp').free,mem_available(),time.monotonic()-self.start)
  if why:raise Refusal(why)
 def stop(self):self.done.set();self.thread.join(timeout=3)
def captured_guard(names):
 out={}
 for n in names:
  for root in (OUT/'lib',PKG,TOOL):
   for suffix in SUFFIXES:
    if ACTIVE_WATCH is not None:ACTIVE_WATCH.check()
    p=root/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file(),'non-file dependency candidate '+str(p));out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:out[str(p)]=None
 return out
def validate_reports(text, expected=None):
 if expected is None:expected=REPORTS
 pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S);free=re.findall(r"'([^']+)' does not depend on any axioms",text);names=[name for name,_ in pairs]+free
 need(len(names)==len(expected) and len(set(names))==len(names) and set(names)==set(expected),'unexpected/duplicate axiom report set')
 for name,body in pairs:
  found={x.strip() for x in body.split(',') if x.strip()};need(found<=AXIOMS,'unexpected axiom '+name+': '+str(found))
def write_state(out,state):
 with (out/'state.tmp').open('w') as f:json.dump(state,f,sort_keys=True,indent=2);f.write('\n')
 os.replace(out/'state.tmp',out/'state.json')
def create_owned_state(out):
 state={'status':'STARTING','rows':[]};out.mkdir(mode=0o700)
 try:write_state(out,state)
 except BaseException as e:
  state['status']='FAILED';state['failure']=repr(e)
  try:write_state(out,state)
  except BaseException as receipt_error:print('FAILED_TO_RECORD_INITIAL_STATE',repr(receipt_error),file=sys.stderr,flush=True)
  raise
 return state
def mark_failed(state,error,elapsed):
 state['status']='FAILED';state['failure']=repr(error);state['elapsed_seconds']=round(elapsed,3)
def record_child_result(row,kind,res,log,save):
 res['log']=str(log)
 try:res['log_sha256']=sha(log,watch_resources=False)
 except BaseException as e:res['log_hash_error']=repr(e)
 row[kind]=res;save(force=True)
 need('log_hash_error' not in res,'unable to hash '+kind+' log')
def source_imports(p):
 result=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):result.extend(line.split('--',1)[0].split()[1:])
 return result
def git_query(*args):
 return subprocess.check_output(['git',*args],cwd=ROOT,timeout=30)
def preflight(require_fresh=True):
 for p,h in ((PLAN,PLAN_PIN),(MON,MON_PIN),(CLIENT,CLIENT_PIN),(INSPECT,INSPECT_PIN),(AUDIT,AUDIT_PIN),(AUDIT_RESULT,AUDIT_RESULT_PIN),(LEAN,LEAN_PIN)):need(p.is_file() and sha(p)==h,'pin drift '+str(p))
 if require_fresh:need(not os.path.lexists(OUT),'output already exists')
 need(sha(D/'research/current14-k215-fwd10to15-split-check/plan.json')=='43adcfd47849e71d94547694bc4faef3d8f4f7cadbb93c521716ed3fe9e89152','remaining fwd audit pin '+'research/current14-k215-fwd10to15-split-check/plan.json')
 need(sha(D/'research/current14-k215-fwd10to15-split-check/attempt01/state.json')=='7ed7dc98ce16735e5f9d57d8208ea1ee3aa52d914394eda7e8196a8cc63d959d','remaining fwd audit pin '+'research/current14-k215-fwd10to15-split-check/attempt01/state.json')
 need(sha(D/'research/current14-k215-fwd10to15-split-check/attempt01/outer-result.json')=='b62b36fc61e99f66ca07d4ddd4b5c95b3bbec198e98cca3fd50231ad972bdb7b','remaining fwd audit pin '+'research/current14-k215-fwd10to15-split-check/attempt01/outer-result.json')
 need(sha(D/'reviews/current14-k215-fwd10to15-split-source-independent/check.py')=='c1a102436560e3516defad1ef42ea88e0ae15afd5546c710ba001d6066d885e0','remaining fwd audit pin '+'reviews/current14-k215-fwd10to15-split-source-independent/check.py')
 need(sha(D/'reviews/current14-k215-fwd10to15-split-source-independent/source-pins.json')=='a7fc1da5a040e6beb732334e783a670fb3e434d4407c1a54b8c1ecce51d0dae1','remaining fwd audit pin '+'reviews/current14-k215-fwd10to15-split-source-independent/source-pins.json')
 need(sha(D/'reviews/current14-k215-fwd10to15-split-terminal-independent/check.py')=='e39b3c5c2efb2805839ef42a0de93a95c6868b459c04f75f9e0352f6f2a3053a','remaining fwd audit pin '+'reviews/current14-k215-fwd10to15-split-terminal-independent/check.py')
 need(sha(D/'reviews/current14-coherent-extension-refactor-retry01-failure-independent/check.py')=='8df927c0e3184e36345bdac558c9c8283697484811613d3301ab05b18c1a19cd','remaining fwd audit pin '+'reviews/current14-coherent-extension-refactor-retry01-failure-independent/check.py')
 need(sha(D/'research/current14-k215-fwd09-split-retry01-check/plan.json')=='20a3d72344b251484b5fddda58a1cb484b79b5c49d704eb311db9e710f8b78ce','second refactor audit pin '+'research/current14-k215-fwd09-split-retry01-check/plan.json')
 need(sha(D/'research/current14-k215-fwd09-split-retry01-check/attempt01/state.json')=='607b1d847954d5dd613e870e11bd537cf6122a0be80a8c389660f84ee001acbe','second refactor audit pin '+'research/current14-k215-fwd09-split-retry01-check/attempt01/state.json')
 need(sha(D/'research/current14-k215-fwd09-split-retry01-check/attempt01/outer-result.json')=='f16e5cb90199ca908ec429d54d13ddd39429375a9eadcfb5bea6b813e392a7c6','second refactor audit pin '+'research/current14-k215-fwd09-split-retry01-check/attempt01/outer-result.json')
 need(sha(D/'reviews/current14-k215-fwd09-split-retry01-source-independent/check.py')=='1488bad7ffbb257fea3cc854741e9837ff98f3c4fa5a1b47a4bc8d10f14c7c52','second refactor audit pin '+'reviews/current14-k215-fwd09-split-retry01-source-independent/check.py')
 need(sha(D/'reviews/current14-k215-fwd09-split-retry01-terminal-independent/check.py')=='29f399e352c5769f7fa0bdefcc168def020ce051b7931891944f7485c23be343','second refactor audit pin '+'reviews/current14-k215-fwd09-split-retry01-terminal-independent/check.py')
 need(sha(D/'reviews/current14-coherent-extension-refactor-failure-independent/check.py')=='4808f4a1622b1a49ddf6ff6031e08c55d6061252db89aecb989d1f1860ca8df0','second refactor audit pin '+'reviews/current14-coherent-extension-refactor-failure-independent/check.py')
 need(sha(D/'research/current14-coherent-extension-runner/plan.json')=='0f44fb7be1c0b7deb24f7ea5a57a7be91820379f51edb6ee63cecdd424c659e9','prior proof/refactor pin '+'research/current14-coherent-extension-runner/plan.json')
 need(sha(D/'research/current14-k215-wf-compatibility-check/plan.json')=='a5c9ff7db8797261682e99d6c2c17ef4ffc831923a1529dbe17cbe57cf473adf','prior proof/refactor pin '+'research/current14-k215-wf-compatibility-check/plan.json')
 need(sha(D/'research/current14-k215-wf-compatibility-check/attempt01/state.json')=='6177e237b922ee419d43d951bc8bf25223ad8b30c925a169d2da4f4e1511057a','prior proof/refactor pin '+'research/current14-k215-wf-compatibility-check/attempt01/state.json')
 need(sha(D/'research/current14-k215-wf-compatibility-check/attempt01/outer-result.json')=='42f70b8c2f7a41225b2f14837db12b2510e77bce215a02df0b21f71425db2b39','prior proof/refactor pin '+'research/current14-k215-wf-compatibility-check/attempt01/outer-result.json')
 need(sha(D/'reviews/current14-k215-wf-compatibility-source-independent/check.py')=='bf3746d938169862becbae1099d10fd43324188cc3017c1e37f971a4f3689d8b','prior proof/refactor pin '+'reviews/current14-k215-wf-compatibility-source-independent/check.py')
 need(sha(D/'reviews/current14-k215-wf-compatibility-terminal-independent/check.py')=='306cabfbe860dc1abc57d07abd2aff5a2735f64e219f196362cd069c6ac60c8c','prior proof/refactor pin '+'reviews/current14-k215-wf-compatibility-terminal-independent/check.py')
 need(sha(D/'reviews/current14-coherent-extension-runner-failure-independent/check.py')=='4b340bdcbc9c627143190f33fb7249084723180e3e14016f35f04164367781c5','prior proof/refactor pin '+'reviews/current14-coherent-extension-runner-failure-independent/check.py')
 raw=subprocess.run([sys.executable,'-I','-S','-B',str(INSPECT)],cwd=ROOT,capture_output=True,timeout=120)
 need(raw.returncode==0 and not raw.stderr,'survey failed: '+raw.stderr.decode(errors='replace')[:500]);obs=json.loads(raw.stdout);need(obs['status']=='OBSERVATION_NOT_BUILD_READINESS','survey status')
 f=obs['fresh'];q=obs['quoted'];h=obs['host'];need(not f['point_in_time_issues'] and not f['workspace_source_drift'] and not f['workspace_source_missing'],'fresh base drift')
 for key in ('issues','namespace_object_hash_conflicts','captured_external_route_conflicts','declared_direct_import_mismatches','traced_without_workspace_source_copy','traced_without_git_tracked_source_copy','traced_without_clean_head_source_copy','source_disagreements_with_host'):need(not q[key],'quoted survey '+key)
 for key in ('external_missing','untracked_source_modules','source_modules_differing_from_head','missing_project'):need(not h[key],'host survey '+key)
 need(obs['pins']['git_head_before']==obs['pins']['git_head_after'],'HEAD changed during survey')
 plan=json.loads(PLAN.read_text());entries=plan['entries'];names=[r['module'] for r in entries];need(len(names)==522 and len(set(names))==522,'refactor plan inventory');fwd_helpers=['BusyBeaver.ZFC.KSource215Fwd09Left','BusyBeaver.ZFC.KSource215Fwd09Right'];more_fwd_helpers=[f'BusyBeaver.ZFC.KSource215Fwd{k}{side}' for k in range(10,16) for side in ('Left','Right')];helper_names=['BusyBeaver.ZFC.KSource215WfTables']+[f'BusyBeaver.ZFC.KSource215WfChunk{k:02d}' for k in range(16)]+['BusyBeaver.ZFC.KSource215WfAssembly'];need([n for n in names if n not in helper_names+fwd_helpers+more_fwd_helpers]==obs['union']['observed_union_topological_order'],'original 490 stage order drift');idx=names.index('BusyBeaver.ZFC.KSource215Data');need(names[idx-18:idx]==helper_names,'helper placement drift');oldplan=json.loads((R/'current14-coherent-extension-runner/plan.json').read_text());oldrows={e['module']:e for e in oldplan['entries']};newrows={e['module']:e for e in entries};need(all(newrows[n]==e for n,e in oldrows.items() if n not in ['BusyBeaver.ZFC.KSource215Data']+[f'BusyBeaver.ZFC.KSource215FwdCheck{k:02d}' for k in range(9,16)]),'non-target source or metadata drift');cp=json.loads((R/'current14-k215-wf-compatibility-check/plan.json').read_text());need([newrows[n] for n in helper_names]==cp['entries'][:18],'helper plan drift');prior=oldrows['BusyBeaver.ZFC.KSource215Data'];expected=next(e.copy() for e in cp['entries'] if e['module']=='BusyBeaver.ZFC.KSource215Data');expected['origin']=prior['origin'];expected['old_parent_status']=prior['old_parent_status'];need(newrows['BusyBeaver.ZFC.KSource215Data']==expected,'K215 source refactor plan drift');need(sha(ROOT/prior['source'])==prior['source_sha256'],'original K215 source drift');fidx=names.index('BusyBeaver.ZFC.KSource215FwdCheck09');need(names[fidx-2:fidx]==fwd_helpers,'fwd helper placement drift');sp=json.loads((R/'current14-k215-fwd09-split-retry01-check/plan.json').read_text());need([newrows[n] for n in fwd_helpers]==sp['entries'][-3:-1],'fwd helper plan drift');fprior=oldrows['BusyBeaver.ZFC.KSource215FwdCheck09'];fexpected=sp['entries'][-1].copy();fexpected['origin']=fprior['origin'];fexpected['old_parent_status']=fprior['old_parent_status'];need(newrows['BusyBeaver.ZFC.KSource215FwdCheck09']==fexpected and sha(ROOT/fprior['source'])==fprior['source_sha256'],'fwd original/refactor plan drift');six=json.loads((R/'current14-k215-fwd10to15-split-check/plan.json').read_text());sixrows={e['module']:e for e in six['entries']};need([newrows[n] for n in more_fwd_helpers]==[sixrows[n] for n in more_fwd_helpers],'six-fwd helper plan drift');[(need(names[names.index(f'BusyBeaver.ZFC.KSource215FwdCheck{k}')-2:names.index(f'BusyBeaver.ZFC.KSource215FwdCheck{k}')]==[f'BusyBeaver.ZFC.KSource215Fwd{k}Left',f'BusyBeaver.ZFC.KSource215Fwd{k}Right'],'six-fwd helper placement drift'),need(newrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}']==dict(sixrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}'],origin=oldrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}']['origin'],old_parent_status=oldrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}']['old_parent_status']) and sha(ROOT/oldrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}']['source'])==oldrows[f'BusyBeaver.ZFC.KSource215FwdCheck{k}']['source_sha256'],'six-fwd original/refactor drift')) for k in range(10,16)]
 base=json.loads((BASE/'state.json').read_text());base_rows={r['module']:r for r in base['records']};need(len(base_rows)==1000 and not set(names)&set(base_rows),'base inventory')
 need(sum(e['old_parent_status']=='FAILED' for e in entries)==7,'seven partial-parent stages must rebuild')
 tracked=set(git_query('ls-files','-z').decode().split('\0'));head=git_query('rev-parse','HEAD').decode().strip();dirty=set(git_query('diff','--name-only',head,'--').decode().splitlines());seen=set()
 for e in entries:
  n=e['module'];p=ROOT/e['source'];need(not Path(e['source']).is_absolute() and p.resolve().is_relative_to(ROOT) and e['source'] in tracked and e['source'] not in dirty and p.is_file() and sha(p)==e['source_sha256'],'source pin/tracking '+n);need(source_imports(p)==e['imports'] or sorted(source_imports(p))==sorted(e['imports']),'source import mismatch '+n)
  for dep in e['imports']:
   if dep in names:need(dep in seen,'bad build order '+n+' -> '+dep)
   else:need(dep in base_rows or dep in plan['external_direct'],'unplanned direct input '+n+' -> '+dep)
  seen.add(n)
 need(len(plan['external_direct'])==99 and 'Init' in plan['external_direct'],'external inventory')
 for n,v in plan['external_direct'].items():
  options=[root/(n.replace('.','/')+'.olean') for root in (PKG,TOOL)];hits=[p for p in options if p.is_file()];need(hits,'external object missing '+n)
  selected=hits[0];need(str(selected.resolve())==v['realpath'] and sha(selected)==v['sha256'],'external object drift '+n)
 for top in {n.split('.')[0] for n in set(base_rows)|set(names)}:
  for root in (PKG,TOOL):
   need(not os.path.lexists(root/top),'project namespace shadow '+str(root/top))
 audit_imports=['DiophantineConsistency.Current14QuotedTranslatedEndpoint','DiophantineConsistency.CurrentWitnessEquivalence2011','DiophantineConsistency.ObjectCurrentEquation2011'];need(source_imports(CLIENT)==audit_imports,'audit client imports');need(all(n in seen or n in base_rows for n in audit_imports),'audit client input absent');need('DiophantineConsistency.Current14CoherentAudit' not in seen and 'DiophantineConsistency.Current14CoherentAudit' not in base_rows,'audit module collision')
 why=decision(shutil.disk_usage('/tmp').free,mem_available(),0);need(why is None,'resource refusal '+str(why))
 return plan,base_rows,obs

def self_test():
 need(decision(DISK_FLOOR,MEM_FLOOR,0)=='disk_floor','disk boundary')
 need(decision(DISK_FLOOR+1,MEM_FLOOR-1,0)=='host_memory_floor','memory boundary')
 need(decision(DISK_FLOOR+1,MEM_FLOOR,TOTAL_SECONDS)=='total_timeout','time boundary')
 need(decision(DISK_FLOOR+1,MEM_FLOOR,0) is None,'safe boundary')
 sample='\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in REPORTS);validate_reports(sample)
 for bad in (sample.replace('propext','sorryAx',1),sample.replace(REPORTS[0],'wrong.name',1),sample+'\n'+sample.splitlines()[0]):
  try:validate_reports(bad)
  except Refusal:continue
  raise Refusal('bad axiom report accepted')
 print(json.dumps({'status':'PASS_SYNTHETIC_CONTROLS','scope':'Pure guard/report controls; no Lean or build output.'},sort_keys=True))

def run():
 global ACTIVE_WATCH
 start=time.monotonic();watch=Watch(start);watch.begin();ACTIVE_WATCH=watch;state=None
 def save(force=False):
  if not force:watch.check()
  write_state(OUT,state)
 try:
  watch.check();plan,base_rows,obs=preflight();watch.check();no_live_lean();watch.check();state=create_owned_state(OUT);watch.check();links={};state.update({'status':'RUNNING','scope':'Coherent project build over audited base using proof-refactored KSource215Data and KSource215FwdCheck09–15 and 32 helper modules; all other 482 project stages unchanged. Package-transitive, dynamic-loading and between-sample mutations remain inherited. No raw TeX/PDF claim or byte-identical original build claim.','plan_sha256':sha(PLAN),'runner_sha256':sha(__file__),'monitor_sha256':sha(MON),'base_state_sha256':sha(BASE/'state.json'),'started_wall_seconds':time.time(),'base_links':links})
  save()
  for name in ('src','lib','logs'):watch.check();(OUT/name).mkdir()
  # Link only authenticated base outputs into this new empty tree.
  b=json.loads((BASE/'state.json').read_text())
  for guards in b['outputs'].values():
   for raw,v in guards.items():
    watch.check()
    if v is None:continue
    src=Path(raw);need(src.is_relative_to(BASE/'lib') and src.is_file() and str(src.resolve())==v['realpath'] and sha(src)==v['sha256'],'base output drift '+raw)
    dst=OUT/'lib'/src.relative_to(BASE/'lib');dst.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(dst),'base link collision '+str(dst));dst.symlink_to(src.resolve());links[str(dst)]={'realpath':str(dst.resolve()),'sha256':v['sha256']}
  need(len(links)>=1000,'base link inventory');save()
  # Snapshot the 522 selected clean tracked sources; new files are exclusive.
  entries=list(plan['entries']);audit_entry={'module':'DiophantineConsistency.Current14CoherentAudit','source':str(CLIENT.relative_to(ROOT)),'source_sha256':CLIENT_PIN,'imports':source_imports(CLIENT),'origin':'audit','old_parent_status':None};entries.append(audit_entry)
  for e in entries:
   watch.check();src=ROOT/e['source'];need(src.is_file() and sha(src)==e['source_sha256'],'snapshot source drift '+e['module']);dst=OUT/'src'/(e['module'].replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
   with src.open('rb') as inp,dst.open('xb') as dstf:
    while True:
     watch.check();block=inp.read(1024*1024)
     if not block:break
     dstf.write(block)
   need(sha(dst)==e['source_sha256'],'snapshot copy mismatch '+e['module'])
  spec=importlib.util.spec_from_file_location('coherent_monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
  env=os.environ.copy()
  for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(OUT/'lib')+':'+str(PKG);env['LEAN_NUM_THREADS']='1'
  completed={};roots=(OUT/'lib',PKG,TOOL)
  for index,e in enumerate(entries):
   watch.check();no_live_lean();n=e['module'];src=OUT/'src'/(n.replace('.','/')+'.lean');obj=OUT/'lib'/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
   for suffix in SUFFIXES:need(not os.path.lexists(OUT/'lib'/(n.replace('.','/')+suffix)),'output/companion collision '+n+suffix)
   row={'module':n,'source_sha256':e['source_sha256'],'origin':e['origin'],'old_parent_status':e['old_parent_status']};state['rows'].append(row);save();print('STAGE',index+1,'/',len(entries),n,flush=True)
   prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M3600','-j1','-DElab.async=false']
   def child(args,kind):
    watch.check();remain=TOTAL_SECONDS-(time.monotonic()-start);need(remain>0,'total timeout');log=OUT/'logs'/(f'{index:03d}-'+n.replace('.','_')+'-'+kind+'.txt');res=monitor.run(prefix+args,OUT,env,log,rss_limit=RSS_LIMIT,mem_floor=MEM_FLOOR,disk_floor=DISK_FLOOR,seconds=min(CHILD_SECONDS,remain),interval=INTERVAL);record_child_result(row,kind,res,log,save);watch.check();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],kind+' failed '+n);return log
   depslog=child(['--deps',str(src)],'deps');records={};counts={}
   for line in depslog.read_text().splitlines():
    p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dependency path '+line)
    dep=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[dep]=counts.get(dep,0)+1;need(dep not in records or (dep=='Init' and counts[dep]<=2 and records[dep]['path']==line),'duplicate dependency '+dep);records[dep]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
   need('Init' in records and set(records)-{'Init'}==set(e['imports'])-{'Init'},'direct dependency set '+n)
   for dep,v in records.items():
    if dep=='Init':expected=plan['external_direct']['Init'];need(v['realpath']==expected['realpath'] and v['sha256']==expected['sha256'],'Init route');continue
    candidates=[r/(dep.replace('.','/')+'.olean') for r in roots if (r/(dep.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==v['path'],'first dependency route '+dep)
    if dep in completed:expected={'realpath':str((OUT/'lib'/(dep.replace('.','/')+'.olean')).resolve()),'sha256':completed[dep]}
    elif dep in base_rows:expected={'realpath':str((BASE/'lib'/(dep.replace('.','/')+'.olean')).resolve()),'sha256':base_rows[dep]['object_sha256']}
    else:need(dep in plan['external_direct'],'unknown external '+dep);expected=plan['external_direct'][dep]
    need(v['realpath']==expected['realpath'] and v['sha256']==expected['sha256'],'producer mismatch '+n+' -> '+dep)
   row['dependencies']=records;row['direct_guard']=captured_guard(records);save();log=child(['--root='+str(OUT/'src'),str(src),'-o',str(obj)],'compile');text=log.read_text();need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",text) and obj.is_file(),'compile diagnostics '+n);need(captured_guard(records)==row['direct_guard'],'direct guard drift '+n)
   if e['origin']=='audit':validate_reports(text)
   elif n.startswith('BusyBeaver.ZFC.KSource215WfChunk'):validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfChunk'+n[-2:]])
   elif n=='BusyBeaver.ZFC.KSource215WfAssembly':validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfNodes','SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfCheck222'])
   elif n=='BusyBeaver.ZFC.KSource215Data':validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.wfCheck222','SetTheory.BusyBeaver.ZFC.KSource215.wf222','SetTheory.BusyBeaver.ZFC.KSource215.path_iff_iter'])
   elif n=='BusyBeaver.ZFC.KSource215Fwd09Left':validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.fwd9Left_ok'])
   elif n=='BusyBeaver.ZFC.KSource215Fwd09Right':validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.fwd9Right_ok'])
   elif n=='BusyBeaver.ZFC.KSource215FwdCheck09':validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok9'])
   elif re.fullmatch(r'BusyBeaver\.ZFC\.KSource215Fwd1[0-5](Left|Right)',n):
    k,side=re.search(r'Fwd(1[0-5])(Left|Right)$',n).groups();validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.fwd'+k+side+'_ok'])
   elif re.fullmatch(r'BusyBeaver\.ZFC\.KSource215FwdCheck1[0-5]',n):validate_reports(text,['SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok'+n[-2:]])
   row['object_sha256']=sha(obj);row['output_guard']={}
   for suffix in SUFFIXES:
    p=OUT/'lib'/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file() and not p.is_symlink(),'bad output companion '+str(p));row['output_guard'][str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:row['output_guard'][str(p)]=None
   completed[n]=row['object_sha256'];save();print('PASS',n,flush=True)
  need(len(completed)==523 and sum(r['old_parent_status']=='FAILED' for r in state['rows'])==7,'compiled inventory')
  # Recheck every output, selected source, direct guard, and base symlink.
  for e,row in zip(entries,state['rows']):
   watch.check();n=e['module'];need(sha(ROOT/e['source'])==e['source_sha256'] and sha(OUT/'src'/(n.replace('.','/')+'.lean'))==e['source_sha256'],'source postflight '+n);need(sha(OUT/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and captured_guard(row['dependencies'])==row['direct_guard'],'output/direct postflight '+n)
   for raw,v in row['output_guard'].items():
    p=Path(raw)
    if v is None:need(not os.path.lexists(p),'unexpected output companion '+raw)
    else:need(p.is_file() and not p.is_symlink() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'output companion drift '+raw)
   for kind in ('deps','compile'):need(sha(row[kind]['log'])==row[kind]['log_sha256'],'log postflight '+n)
  for raw,v in links.items():
   watch.check();p=Path(raw);need(p.is_symlink() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'base link postflight '+raw)
  # Repeat the full pinned read-only survey; this does not authenticate transitive package/dynamic loading.
  watch.check();plan2,base2,obs2=preflight(require_fresh=False);need(plan2==plan and set(base2)==set(base_rows),'postflight plan/base drift');watch.check()
  state['status']='PASS';state['elapsed_seconds']=round(time.monotonic()-start,3);save();print('PASS coherent eight-refactor 522-stage extension and axiom client',flush=True)
 except BaseException as e:
  if state is not None:
   mark_failed(state,e,time.monotonic()-start)
   try:save(force=True)
   except BaseException as receipt_error:print('FAILED_TO_RECORD_STATE',repr(receipt_error),file=sys.stderr,flush=True)
  raise
 finally:ACTIVE_WATCH=None;watch.stop()

if __name__=='__main__':
 try:
  if sys.argv[1:]==['--self-test']:self_test()
  elif sys.argv[1:]==['--preflight']:
   plan,_,obs=preflight();print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stages':len(plan['entries']),'partial_parent_stages_to_rebuild':7,'disk_free':obs['resources']['tmp_free_bytes'],'memory_available':obs['resources']['mem_available_bytes'],'disk_stop_threshold':DISK_FLOOR,'scope':'No Lean or output created. Package-transitive/dynamic ancestry and build success remain unproved.'},sort_keys=True))
  elif sys.argv[1:]==['--run']:run()
  else:raise Refusal('use --self-test, --preflight or --run')
 except BaseException as e:
  print('REFUSED_OR_FAILED',repr(e),file=sys.stderr);raise
