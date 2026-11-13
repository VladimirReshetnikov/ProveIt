#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(pathlib.Path(p).read_text())
def guards(g):
 for k,v in g.items():
  p=pathlib.Path(k)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
B=R/'thirteen-current2011-fresh-model/attempt01';b=load(B/'state.json');o=load(B/'outer-terminal.json')
assert (b['status'],o['session_id'],o['exit_code'])==('FAILED',85883,1) and len(b['records'])==7
names=['FrontierBridge','DiophantineConsistency.ThirteenCarrier','DiophantineConsistency.ArithmeticOddOrdinateResidue','DiophantineConsistency.ArithmeticPellPigeonhole','DiophantineConsistency.ArithmeticThirteenSeed','DiophantineConsistency.ArithmeticThirteenOuter','DiophantineConsistency.ModelThirteenRestoration']
assert [x['module'] for x in b['records']]==names
for x in b['records']:
 for run in [x['deps_run'],x['compile_run']]: assert run['exit']==0 and sha(run['log'])==run['log_sha256']
 cmd=x['compile_run']['command'];assert sha(cmd[cmd.index('-o')+1])==x['object_sha256']
 assert sha(B/'src'/pathlib.Path(x['module'].replace('.','/')+'.lean'))==x['source_sha256']
 guards(x['direct_guard'])
a=b['active'];assert a['module']=='DiophantineConsistency.ModelThirteenCarrier' and a['compile_run']['exit']==-6
assert sha(a['compile_run']['log'])==a['compile_run']['log_sha256'] and 'memory_exception' in pathlib.Path(a['compile_run']['log']).read_text()
assert sha(a['deps_run']['log'])==a['deps_run']['log_sha256'] and a['deps_run']['exit']==0
guards(a['direct_guard_before'])
for module,h in b['snapshot'].items():assert sha(B/'src'/pathlib.Path(module.replace('.','/')+'.lean'))==h
checks=[('thirteen-carrier-import-probe',88369,0,'PASS',[0,0]),('thirteen-current2011-complete-only-draft/attempt01',35336,1,'FAILED',[0,-6]),('thirteen-current2011-seed-construction-draft/attempt01',22429,1,'FAILED',[0,124])];out=[]
for n,session,outer,status,exits in checks:
 p=R/n;d=load(p/'state.json');t=load(p/'outer-terminal.json');assert (d['status'],t.get('actual_session',t.get('session_id')),t['exit_code'])==(status,session,outer)
 assert [x['exit'] for x in d['runs']]==exits
 for x,log in zip(d['runs'],['deps.txt','compile.txt']):assert sha(p/log)==x['log_sha256']
 guards(d['direct_guard'])
 for k,v in d.get('overlay_links',{}).items():assert pathlib.Path(k).is_symlink() and str(pathlib.Path(k).resolve())==v,k
 if status=='PASS':
  c=d['runs'][-1]['command'];assert sha(c[c.index('-o')+1])==d['object_sha256'] and d['preflight_before_sha256']==d['preflight_after_sha256']
 out.append({'name':n,'session':session,'outer_exit':outer,'child_exits':exits,'guard_slots':len(d['direct_guard']),'overlay_links':len(d.get('overlay_links',{})),'state_sha256':sha(p/'state.json')})
i=R/'thirteen-carrier-import-probe';src=(B/'src/DiophantineConsistency/ModelThirteenCarrier.lean').read_text();probe=(i/'CarrierImports.lean').read_text();imports=lambda s:re.findall(r'^import .+$',s,re.M)
assert imports(src)==imports(probe) and probe.strip().endswith('#check True') and (i/'compile.txt').read_text().strip()=='True : Prop'
assert sha(i/'deps.txt')==a['deps_run']['log_sha256']
assert sha(R/'thirteen-current2011-complete-only-draft/ModelThirteenComplete.lean')=='6188f27280f4bf958c846b7550ae1d4a40487bd929d2d5bb29c6e4d86d0dccd6'
only=(R/'thirteen-current2011-complete-only-draft/ModelThirteenComplete.lean').read_text();factored=(R/'thirteen-current2011-complete-factored-draft/ModelThirteenCarrier.lean').read_text();end='end DiophantineConsistency.ModelThirteenCarrier\n'
assert only.endswith(end) and factored.startswith(only[:-len(end)]) and 'theorem complete ' in only and 'theorem sameNoZero69' not in only
assert sha(R/'thirteen-current2011-seed-construction-draft/ModelThirteenSeedConstruction.lean')=='06f00485f5991ff193561f2d6c5da33e11ba554f7a75247534f04ffe421752f1'
print(json.dumps({'status':'PASS','initial_session':85883,'initial_completed_rows':names,'active_child_exit':-6,'diagnostics':out,'scope':'Captured source/receipt review only; no Lean replay or completion theorem.'},indent=2))
