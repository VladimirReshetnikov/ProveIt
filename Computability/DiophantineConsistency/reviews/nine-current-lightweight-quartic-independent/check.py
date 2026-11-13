#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-current-lightweight-quartic-probe';A=P/'attempt01';SRC=P/'src/DiophantineConsistency';BASE=D/'research/thirteen-current2011-complete-4g-retry/attempt03/state.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='f9c43d3dc6da91c65426e01e7e1c247ddd2a554f63c6f88f183bb8fc32c1a411'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',91524,0)
assert sha(P/'run.py')==d['runner_sha256']=='be141d753f3c4d92bdcfaafff14017cfb8078836f4734cc0a040328f5bc4cb30'
assert sha(BASE)==d['base_state_sha256']=='c0963c19b50b76cc2e43655659ae259baeec6d0154ee3381e843ec317dc35466'
names=['QuarticCompilerCore','QuarticSyntaxCore','GatesSemiring','QuarticSemiring','NineLightQuartic'];pins=['699d642301db4fd06012f7b1b63f80f6793b5986cc36f285fddf00c63456e610','e7b4e5256523bec1dea0f9fd4ca670d403b24df419d568fb4ba07136b5eb80f9','5dca514566a094b5cfd45f51201af7c73826e4779114f5218fc9737c9fc059d2','94bf6610873f3b7b5481f86f19ba66807a79f8c02cd48d44a764410702d1176b','1765f6e61a43746453db988c75056896b82e12fea4766014c8c523fcdf435790'];assert [r['module'] for r in d['rows']]==names
objects={}
for row,n,pin in zip(d['rows'],names,pins):
 source=SRC/(n+'.lean');assert sha(source)==row['source_sha256']==pin
 assert sha(pathlib.Path('/tmp/nine-light-quartic-probe-20261105/src/DiophantineConsistency')/(n+'.lean'))==pin
 imports=set(re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M));assert set(row['dependencies'])-{'Init'}==imports-{'Init'}
 assert set((A/(n+'-deps.txt')).read_text().splitlines())=={v['path'] for v in row['dependencies'].values()}
 assert 'error:' not in (A/(n+'-compile.txt')).read_text() and 'sorryAx' not in (A/(n+'-compile.txt')).read_text()
 if n!='NineLightQuartic':assert sha(D/'Lean/DiophantineConsistency'/(n+'.lean'))==pin
 for label in ('deps','compile'):
  run=row[label];log=A/(n+'-'+label+'.txt');assert sha(log)==run['log_sha256'] and run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
  assert run['rss_limit_bytes']==4*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==120 and run['sampling_interval_seconds']==0.1
  assert run['peak_session_rss_bytes']<4*1024**3 and run['min_host_available_bytes']>=10*1024**3
 cmd=row['compile']['command'] if 'command' in row['compile'] else None
 obj=pathlib.Path('/tmp/nine-light-quartic-probe-20261105/lib/DiophantineConsistency')/(n+'.olean');assert sha(obj)==row['object_sha256'];objects[n]=row['object_sha256']
 for key,v in row['direct_guard'].items():
  p=pathlib.Path(key)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 for mod,v in row['dependencies'].items():
  if mod.startswith('DiophantineConsistency.') and mod.split('.')[-1] in objects:assert v['sha256']==objects[mod.split('.')[-1]],mod
assert len(d['overlay_links'])==1029
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
s=(SRC/'NineLightQuartic.lean').read_text();old=(D/'Lean/DiophantineConsistency/IPRAQuarticModelBridge.lean').read_text()
a=old.split('private theorem square_syntax',1)[1].split('#print axioms',1)[0];b=s.split('private theorem square_syntax',1)[1].split('#print axioms',1)[0];assert a==b
for fragment in ['[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','theorem expression_eq {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))','theorem zero_iff_residuals {m : ℕ}','theorem exists_quartic_iff {m : ℕ}','∃ v : Fin (witnessCount p q + 1) → V, InternalZero (expression p q) v','∃ v : Fin m → V, p.evalSemiring (Sum.elim Empty.elim v) =','q.evalSemiring (Sum.elim Empty.elim v)']:assert fragment in s,fragment
log=(A/'NineLightQuartic-compile.txt').read_text();assert log.strip()=="'DiophantineConsistency.NineLightQuartic.exists_quartic_iff' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert objects['NineLightQuartic']=='7ac8b9f968ac00677c81d17adb373127631f1bc4614b2abcd57407e181c2af04'
print(json.dumps({'status':'PASS','outer_session':91524,'stage_names':names,'direct_guard_slots':[len(r['direct_guard']) for r in d['rows']],'overlay_links':len(d['overlay_links']),'bridge_object_sha256':objects['NineLightQuartic'],'scope':'Generic IΣ₁ model quartic compilation bridge only; no concrete nine-variable or iPRA endpoint; no Lean replay or full postflight.'},indent=2))
