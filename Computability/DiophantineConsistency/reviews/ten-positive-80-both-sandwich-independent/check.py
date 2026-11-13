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
('pell-scaled-sandwich-prototype','PellScaledSandwich','attempt02','run.py','ab21d0b34b15cc527fee82f7f378578c10f80f1545cff2463e567bd668848db2'),
('ten-positive-80-sandwich-lower-prototype','Direct80SandwichLower','attempt01','run.py','7d5e68582f5f193b54c598abe8b637dcdd603f86bf6a4fc15f2b2404aa1e4dd8'),
('pell-scaled-sandwich-upper-prototype','PellScaledUpper','attempt02','run.py','4682931d4405398aa9630cee05c32307ca9d2cb09063d3e6d73fd9c14d9d5d9d'),
('ten-positive-80-sandwich-both-prototype','Direct80SandwichBoth','attempt02','run.py','e2dc0ceb94d27c0b8d6cf83a346d6a1576baddde0abb409f3c6e375fce9ef5db'),
('ten-positive-scaled-rounding-prototype','ScaledPellRounding','rounding-attempt01','run.py','82f7bdf61fca78c40b05f96de1a12ab5b3451a60cb4e62c4d8c8eaceacd5ecb3'),
('ten-positive-80-population-conditional-prototype','Direct80PopulationConditional','population-attempt01','run.py','cf86b25de9a1695237ba04922811a9dac2b9ce08d6d3d5f3d7e741bdd46a6449'),
('ten-positive-80-population-sandwich-prototype','Direct80PopulationSandwich','populationsandwich-attempt01','run.py','9744fd24f7ff8b0c68ec8f92254336f2c1ca39a60194d20124e3da7e40f046cf'),
('ten-positive-80-population-model-prototype','Direct80PopulationModel','populationmodel-attempt01','run.py','d3f8b1b8d21a972b6e3043b61d7e9125465c2574411d2d97e69155806ba547d8')]

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
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
src=(B/'ten-positive-80-sandwich-both-prototype/Direct80SandwichBoth.lean').read_text()
need(all(x in src for x in ('(h31 : (31:V)≤(p 0:V))','(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hbeta : ∃u : V, (p 0:V)=2*u+1)','graph_sandwich_lower p v hb hl hh hv hz hbeta','have hnr : n=r+1','graph_first_main_alignment p v hb hl hh hv hz hbeta','have hpert : 2*r*3≤A0','have hcrude : 2*r*3*N<A0*D','upper_of_bounds (X p v) r a B A0 hA0 hcoeff hpert hcrude','exact ⟨r,hr,hR,hXeq,hlow,hupper⟩')),'both-sandwich proof scope')
helper=D/'Lean/DiophantineConsistency/ArithmeticHalfBinomial.lean'
need(h(helper)=='9bdc459d8fc174a54e4af5934f7fba67f317e12fe8e7325da76bcdabcf666fa1','source helper pin')
x=helper.read_text();body=x[x.index('theorem seventy_two_lt_exp'):x.index('private theorem dvd_of_add')];need('sigma1_succ_induction' in body and not re.search(r'\bhalf_binomial\b',body),'helper source independence')
model=(B/'ten-positive-80-population-model-prototype/Direct80PopulationModel.lean').read_text();join=(B/'ten-positive-80-population-sandwich-prototype/Direct80PopulationSandwich.lean').read_text()
need(all(x in model for x in ('(hbeta31 : (31:V)≤(p 0:V))','(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)','(hbeta : (p 0:V)+1=Exp.exp d)','graph_sandwich_both p v hbeta31 hl hh hv hz hbetaodd','graph_population_of_sandwich p v d r','hbeta31 hl hh hv hz hbetaodd hd hbeta hr hR hlow hup')),'model same-r join')
need(all(x in join for x in ('ScaledPellRounding.extract (X p v) (Y p v) r','graph_population_of_half_binomial p v d r z','hr hbin')),'rounding and population')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
