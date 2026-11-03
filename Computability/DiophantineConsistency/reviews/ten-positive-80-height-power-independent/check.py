#!/usr/bin/env python3
"""Read-only audit of selected 80-graph transport producers."""
import ast,json,re,sys,os
from pathlib import Path
from hashlib import sha256
if sys.flags.optimize:raise RuntimeError('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
E=[
('pell-variable-growth-prototype','PellVariableGrowth','attempt03','run.py','10b4e07ac9ed327d7367c17f8bd6d49ea89014b804233c63c2d407bac19c30c8'),
('ten-positive-80-variable-height-prototype','Direct80VariableHeight','attempt03','run.py','3dad2c5c21cfe61a123130fb35ba183eb2448732c0550f8d080dfe2f5a375503'),
('ten-positive-80-rank-lower-prototype','Direct80RankLower','attempt03','run.py','5a253042c41445cda3c77cf3cf37ced81de8117d2a956cfcd4b75c68bdb1af68'),
('ten-positive-fixed-beta-lower-prototype','Direct80FixedBetaLower','attempt01','run.py','de5a57966b6c52f0a8b335d58178712df838d485463ac1971d4cf7bfca0b17b6'),
('ten-positive-80-projection-product-prototype','Direct80ProductHeight','height-attempt02','run-height.py','514d4c0cb553bcbf29a97bdc5c19792b60267efbbcf8a7d91ae6a636ba93100c'),
('ten-positive-80-projection-product-prototype','Direct80PowerFromHeight','fromheight-attempt01','run-fromheight.py','fcd76fddee0bf1f62af8bf9e342619f539d12e96e3c2f2ed212174ac43a34ec7'),
('ten-positive-80-projection-product-prototype','Direct80GraphProduct','graph-attempt02','run-graph.py','1c50f0bc8023904c44e4a1e708caef1058c912a97d37a2c74d79c57146cb6483'),
('ten-positive-80-projection-product-prototype','Direct80GraphPower','graphpower-attempt01','run-graphpower.py','7769b721a22240d34b64b4363abae11d77d47074d863a1b860a8b97a49fd7bf6'),
('ten-positive-80-symbolic-port-bounds-prototype','Direct80SymbolicPortBounds','attempt01','run.py','926f002971d186ebfc03bbcba969119793a47dd83bb472aa7efc2742edb40383'),
('ten-positive-80-fixed-symbolic-power-prototype','Direct80FixedSymbolicPower','graphpower-attempt01','run.py','01a151cecb223ec4e353748beaf6df9c57ffb68688ad3fa209f5793fd18d0791')]

out={};imports={};samples=0
for directory,module,attempt,runner,pin in E:
 root=B/directory;obs=root/'observations'/attempt;t=obs/'terminal.json';src=root/(module+'.lean');run=root/runner
 need(h(t)==pin,'terminal '+module);j=json.loads(t.read_text());p=j['pins'];need(j['exit']==0 and j['reason'] is None and p==j['after'],'status '+module)
 need(h(src)==h(obs/'source.txt')==p['source'] and h(run)==p['runner'] and h(L)==p['lean'],'source runner lean '+module)
 need(h(obs/'stdout')==j['stdout_sha256'] and h(obs/'stderr')==j['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 txt=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'diagnostics '+module)
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'axiom report '+module)
 obj=Path(j['output_root'])/(module+'.olean');need(h(obj)==j['object_sha256'],'object '+module);out[module]={'source':p['source'],'object':j['object_sha256'],'path':str(obj),'terminal':pin}
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean');need(h(provider)==p['direct_provider'],'provider '+module)
 tree=ast.parse(run.read_text());assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='extra' for x in n.targets));extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts]
 for n in tree.body:
  if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='extra':extras.extend(Path(ast.literal_eval(x.args[0])) for x in n.value.elts)
  if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='extra' and n.value.func.attr=='append':extras.append(Path(ast.literal_eval(n.value.args[0].args[0])))
 need([h(x) for x in extras]==p['extra'],'predecessors '+module)
 roots=[Path(x) for x in j['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');selected=next((r/rel for r in roots if (r/rel).is_file()),None);need(selected is not None,'missing import '+name)
  if '.' in name:
   ns=next((r for r in roots if (r/name.split('.')[0]).is_dir()),None);need(ns and (ns/rel).is_file(),'shadow '+name)
  imports[module+':'+name]={'path':str(selected),'sha256':h(selected)}
 pre=j['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'preflight')
 for x in j['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2,'sample');samples+=1
# Abstract full-product height estimate has a staged author receipt.
P=B/'ten-positive-80-projection-product-prototype';o=P/'observations/power-attempt02';t=o/'result.json';pin='8f02e4d53dc77de61bd705aaa8ad9ea48e01ed8325c827fdecf7714b272b202c'
need(h(t)==pin,'power receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='PASS' and j['stages']==[st] and st['exit']==0 and st['reason'] is None,'power status')
module='Direct80ProductPower';src=P/(module+'.lean');need(h(src)==h(o/'stage-01.source.lean')==st['source_sha256']==j['sources'][module] and h(P/'run-power.py')==j['runner_sha256'],'power source/runner')
need(h(st['command'][-1])==st['object_sha256'] and h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'] and not (o/'stage-01.stderr').read_bytes(),'power object/log')
txt=(o/'stage-01.stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'power diagnostics')
ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'power axioms')
for path,digest in j['predecessors'].items():need(h(path)==digest,'power predecessor')
base=B/'ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json';need(h(base)=='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f','power base receipt')
lib=Path('/tmp/qcube92-halt-5apqi7f7/lib')
def record(p):return {'sha256':h(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
union={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
need(len(union)==1291 and union==json.loads(base.read_text())['union'],'power provider union')
pre=st['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'power preflight')
for x in st['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'power sample');samples+=1
out[module]={'source':st['source_sha256'],'object':st['object_sha256'],'path':st['command'][-1],'terminal':pin}
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
growth=(B/'pell-variable-growth-prototype/PellVariableGrowth.lean').read_text();height=(B/'ten-positive-80-variable-height-prototype/Direct80VariableHeight.lean').read_text();power=(P/'Direct80ProductPower.lean').read_text();small=(P/'Direct80ProductHeight.lean').read_text()
need(all(x in growth for x in ('private def comparisonDef : 𝚺₁.Semisentence 4','!ArithmeticPow.powerDef e X r','induction r using ISigma1.sigma1_succ_induction','paired_comparison_strict')),'internal induction')
need(all(x in height for x in ('graph_first_main_alignment p v hb hl hh hv hz hbeta','let r : V := n-1','rankNat p v=2*r+1','paired_comparison_strict','power (X p v) (r+1)<Hnat p v')),'height witness')
need(all(x in power for x in ('(hX : 32≤X) (hb : b≤X) (hr : 15≤r)','b*(X+Exp.exp (2*r+1))*(Exp.exp (2*r+1)*X+1)<power X (r+1)')),'whole-product size hypotheses')
need(all(x in small for x in ('b*(X+t)*(t*X+1)<H','|P|','small_divisible_zero','mul_eq_zero.mp hz')),'height and cancellation')
final=(P/'Direct80GraphPower.lean').read_text()
need(all(x in final for x in ('(hbeta31 : (31:V)≤(p 0:V))','(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hbetaodd : ∃u : V, (p 0:V)=2*u+1)','graph_variable_height p v hb hl hh hv hz hbetaodd','half_rank_ge_fifteen (rankNat p v) r','whole_product_lt_power (X p v) (b p v) r','graph_power_of_height p v hb hl hh hv hz','X p v=Exp.exp (rankNat p v)')),'final power binding')
failed=P/'observations/power-attempt01';ft=failed/'result.json';need(h(ft)=='b083b55d581db47d646f539df468ba16bb7bc424b2a5d5e1796152ebe567b280','failed staged receipt');fj=json.loads(ft.read_text());fs=json.loads((failed/'stage-01.json').read_text());need(fj['status']=='FAILED' and fs['exit']!=0 and h(failed/'stage-01.source.lean')==fs['source_sha256'] and h(failed/'stage-01.stdout')==fs['stdout_sha256'] and h(failed/'stage-01.stderr')==fs['stderr_sha256'],'failed staged artifacts')
fixed=(B/'ten-positive-80-fixed-symbolic-power-prototype/Direct80FixedSymbolicPower.lean').read_text()
need(all(x in fixed for x in ('(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)','fixed_bounds (V:=V) p hp0 hp2 hp3','graph_power p v h31 hl hh hv hz hodd','X p v=Exp.exp (rankNat p v)')),'fixed symbolic specialization')
need(imports['Direct80SymbolicPortBounds:Direct80FixedBetaOdd']['sha256']=='e149b06aa8b7d1999e95a1b565441af27b4d8e223e0525d36987172ecbdbdc88','fixed beta odd producer')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
