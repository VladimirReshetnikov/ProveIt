#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-current-lightweight-jones-probe';A=P/'attempt01';SRC=P/'src/DiophantineConsistency';OUT=pathlib.Path('/tmp/nine-light-jones-probe-20261105');Q=D/'research/nine-current-lightweight-quartic-probe/attempt01/state.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());manifest=json.loads((P/'source-manifest.json').read_text());assert sha(P/'source-manifest.json')=='caa4ea787a0707ec2be17297be48b1e0c6a2c87d782e2fe917b17cbbfdab5383' and sha(A/'state.json')=='5003d43d0deb8c7339766d9ea62bb3866a66fba9d4d277fcca5f4afcf0db33d4'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',32748,0) and sha(P/'run.py')==d['runner_sha256']=='6b9942bcce89d29b81086827fa12b84b3ca62a3a3517744ffbe561edf35e7f07'
assert sha(Q)==d['base_state_sha256']=='f9c43d3dc6da91c65426e01e7e1c247ddd2a554f63c6f88f183bb8fc32c1a411'
assert len(d['rows'])==len(manifest['rows'])==20;objects={};slots=0
for row,m in zip(d['rows'],manifest['rows']):
 n=row['module'];assert m['module']=='DiophantineConsistency.'+n;src=SRC/(n+'.lean');assert sha(src)==row['source_sha256']==m['source_sha256']==sha(OUT/'src/DiophantineConsistency'/(n+'.lean'))
 if n!='ModelJonesNine':assert sha(D/'Lean/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']
 imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M);assert imports==m['imports'] and set(row['dependencies'])-{'Init'}==set(imports)-{'Init'}
 for label in ['deps','compile']:
  run=row[label];log=A/(n+'-'+label+'.txt');assert sha(log)==run['log_sha256'] and run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
  assert run['rss_limit_bytes']==4*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==120 and run['sampling_interval_seconds']==0.1 and run['peak_session_rss_bytes']<4*1024**3 and run['min_host_available_bytes']>=10*1024**3
 assert set((A/(n+'-deps.txt')).read_text().splitlines())=={v['path'] for v in row['dependencies'].values()}
 text=(A/(n+'-compile.txt')).read_text();assert 'error:' not in text and 'sorryAx' not in text
 obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');assert sha(obj)==row['object_sha256'];objects[n]=row['object_sha256']
 for mod,v in row['dependencies'].items():
  if mod.startswith('DiophantineConsistency.') and mod.split('.')[-1] in objects:assert v['sha256']==objects[mod.split('.')[-1]],mod
 for key,v in row['direct_guard'].items():
  p=pathlib.Path(key)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 slots+=len(row['direct_guard'])
assert len(d['overlay_links'])==1034
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
assert d['rows'][-1]['dependencies']['DiophantineConsistency.NineLightQuartic']['sha256']=='7ac8b9f968ac00677c81d17adb373127631f1bc4614b2abcd57407e181c2af04'
assert objects['ModelJonesNine']=='9db3f4363700e3d3ec2a7d411884be7c717192218a8d50ab43cc798e2ba1b425'
s=(SRC/'ModelJonesNine.lean').read_text();old=(D/'Lean/DiophantineConsistency/ModelJonesNine.lean').read_text()
old=old.replace('import DiophantineConsistency.IPRAExplicitZFCReduction','import DiophantineConsistency.NineLightQuartic').replace('`QuarticSyntaxFacts`, this discharges `IPRAExplicitZFCReduction.JonesModel`. -/','`QuarticSyntaxFacts`, this gives the generic Jones-model equivalence directly. -/').replace('IPRAQuarticModelBridge.exists_quartic_iff','NineLightQuartic.exists_quartic_iff').replace('IPRAQuarticModelBridge.zero_iff_residuals','NineLightQuartic.zero_iff_residuals')
start='theorem jonesModel : IPRAExplicitZFCReduction.JonesModel := by\n  intro V _ _ m p q';expanded='theorem jonesModel (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]\n    {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :\n    (∃ a : Fin 9 → V,\n      AdaptiveEquationSyntax2011.InternalZero (ExecutableJones.expression (QuarticSyntax.expression p q) 0) a) ↔\n      ∃ v : Fin (QuarticCompiler.witnessCount p q + 1) → V,\n        AdaptiveEquationSyntax2011.InternalZero (QuarticSyntax.expression p q) v := by';assert start in old;assert old.replace(start,expanded)==s
interface=(D/'Lean/DiophantineConsistency/IPRAExplicitZFCReduction.lean').read_text();assert 'def JonesModel : Prop :=\n  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))' in interface
for f in ['(∃ a : Fin 9 → V,','InternalZero (ExecutableJones.expression (QuarticSyntax.expression p q) 0) a) ↔','∃ v : Fin (QuarticCompiler.witnessCount p q + 1) → V,','InternalZero (QuarticSyntax.expression p q) v']:assert f in interface
print(json.dumps({'status':'PASS','outer_session':32748,'successful_stages':len(objects),'guard_slots':slots,'overlay_links':len(d['overlay_links']),'final_object_sha256':objects['ModelJonesNine'],'scope':'Generic all-IΣ₁-model Jones correspondence only; no concrete nine-variable or iPRA endpoint, final axiom report, full postflight or Lean replay.'},indent=2))
