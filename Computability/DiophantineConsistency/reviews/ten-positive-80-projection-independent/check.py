#!/usr/bin/env python3
"""Read-only audit of selected 80-graph transport producers."""
import ast,json,re,sys
from pathlib import Path
from hashlib import sha256
if sys.flags.optimize:raise RuntimeError('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
E=[
('ten-positive-80-projection-divisibility-prototype','Direct80ProjectionDivisibility','attempt01','run.py','4e53e8abbbc3352d710a87bd73280cf2322557ef16d8263967dd11feea24696e'),
('ten-positive-80-natural-projection-prototype','Direct80NaturalProjection','attempt02','run.py','a8d10dd47bfdb81a5c4e74298f5dc95fe37947c2cbafaca4c835be652faf5536'),
('ten-positive-80-projection-pell-prototype','Direct80ProjectionPell','attempt02','run.py','cdbe0eb0e80d2c0cf2740a60defe6a2c9b3b94922af12aecb3ce2f51845046c0'),
('ten-positive-80-projection-product-prototype','Direct80GraphProduct','graph-attempt02','run-graph.py','1c50f0bc8023904c44e4a1e708caef1058c912a97d37a2c74d79c57146cb6483'),
('ten-positive-80-scaled-growth-prototype','Direct80PowerBound','power-attempt02','run-power.py','a9322a46ad88f52e35b5a0cb2ef2550d5e9789b599f53a058a765e4e75fd7e08')]

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
# Abstract product theorem uses a staged author receipt.
P=B/'ten-positive-80-projection-product-prototype';o=P/'observations/product-attempt03';t=o/'result.json';pin='437f0451ff90dc5e265b3a4cab1cf998673b3706b4b48617488c414c60fbdfb0'
need(h(t)==pin,'product receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='PASS' and j['stages']==[st] and st['exit']==0 and st['reason'] is None,'product status')
module='Direct80ProjectionProduct';src=P/(module+'.lean');need(h(src)==h(o/'stage-01.source.lean')==st['source_sha256']==j['sources'][module] and h(P/'run.py')==j['runner_sha256'],'product source/runner')
need(h(st['command'][-1])==st['object_sha256'] and h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'] and not (o/'stage-01.stderr').read_bytes(),'product object/log')
txt=(o/'stage-01.stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'product diagnostics')
ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'product axiom report')
for path,digest in j['predecessors'].items():need(h(path)==digest,'product predecessor')
pre=st['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'product preflight')
for x in st['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'product sample');samples+=1
out[module]={'source':st['source_sha256'],'object':st['object_sha256'],'path':st['command'][-1],'terminal':pin}
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
g=(P/'Direct80GraphProduct.lean').read_text();prod=(P/'Direct80ProjectionProduct.lean').read_text();nat=(B/'ten-positive-80-natural-projection-prototype/Direct80NaturalProjection.lean').read_text()
need(all(x in prod for x in ('(hdiv : (4*a+3) ∣ b*','(4*a+3) ∣ b*(X-t)*(t*X+1)','have htwo : 2*(b*K)=H*(b*X*c-u)','H*(b*K)-(2*a+1)*(2*(b*K))','hnormdiv')),'whole-product formula')
need(all(x in g for x in ('(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','ι (b p v)*(ι (X p v)-ι (Exp.exp (rankNat p v)))','graph_projection_pell p v hb hl hh hv hz','graph_positive_gap p v hb hv hz','Direct80ProjectionProduct.entire_product')),'graph product scope')
need(all(x in nat for x in ('Hnat p v∣b p v*Knat p v','natural_dvd_of_signed','nonneg_or_nonpos t','tsub_add_cancel_of_le h4A','tsub_add_cancel_of_le (le_of_lt hgap)')),'natural binding')
# Record retained stage failures: broad-import attempt01 was killed, attempt02 failed.
for attempt,pin in [('product-attempt01','b67186ebe4b2828ca05979aa119458194b72c761b872720e128755e6eda72716'),('product-attempt02','040e1c7f47fb0f8029abad4a5e1c415b2e2c5aab8029798c31f098816e9ae036')]:
 o=P/'observations'/attempt;t=o/'result.json';need(h(t)==pin,'failed product receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='FAILED' and st['exit']!=0 and h(o/'stage-01.source.lean')==st['source_sha256'] and h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'],'failed product artifacts')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  if directory=='ten-positive-80-scaled-growth-prototype' and not path.parent.name.startswith('power-'):continue
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
