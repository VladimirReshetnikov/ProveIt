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
('ten-positive-80-natural-transport-prototype','Direct80NaturalTransport','graphpower-attempt02','run.py','5b9d15d9a0aed355886902c07ce0f215c3c31de5a3f5e8825f0e7723e49f378a'),
('ten-positive-80-projection-product-prototype','Direct80RadixAlignment','radix-attempt01','run-radix.py','123984d6fb939f1ba6e22ccb55eec1a5dff3ca3e614261870a566df2ecf03b39'),
('ten-positive-80-repunit-prototype','Direct80Repunit','repunit-attempt01','run.py','d7776c4f213e215a2030c3c6f4e66194ade4ff55819a6cd080df0c0e5148e5b5'),
('ten-positive-80-rank-three-prototype','Direct80RankThree','rankthree-attempt01','run.py','4b02eba33d01833b1774094d268bcb067969b99c1eb02a3d1b650ee81a434fce'),
('ten-positive-80-population-conditional-prototype','Direct80PopulationConditional','population-attempt01','run.py','cf86b25de9a1695237ba04922811a9dac2b9ce08d6d3d5f3d7e741bdd46a6449'),
('pell-scaled-sandwich-prototype','PellScaledSandwich','attempt02','run.py','ab21d0b34b15cc527fee82f7f378578c10f80f1545cff2463e567bd668848db2'),
('ten-positive-80-sandwich-lower-prototype','Direct80SandwichLower','attempt01','run.py','7d5e68582f5f193b54c598abe8b637dcdd603f86bf6a4fc15f2b2404aa1e4dd8'),
('pell-scaled-sandwich-upper-prototype','PellScaledUpper','attempt02','run.py','4682931d4405398aa9630cee05c32307ca9d2cb09063d3e6d73fd9c14d9d5d9d'),
('ten-positive-scaled-rounding-prototype','ScaledPellRounding','rounding-attempt01','run.py','82f7bdf61fca78c40b05f96de1a12ab5b3451a60cb4e62c4d8c8eaceacd5ecb3')]

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
rep=(B/'ten-positive-80-repunit-prototype/Direct80Repunit.lean').read_text();pop=(B/'ten-positive-80-population-conditional-prototype/Direct80PopulationConditional.lean').read_text();low=(B/'ten-positive-80-sandwich-lower-prototype/Direct80SandwichLower.lean').read_text();up=(B/'pell-scaled-sandwich-upper-prototype/PellScaledUpper.lean').read_text();rounding=(B/'ten-positive-scaled-rounding-prototype/ScaledPellRounding.lean').read_text()
need(all(x in rep for x in ('graph_radix_alignment p v d','obtain ⟨N,hN,hq,hbound,hrest⟩','v 0=rep d N','(hbeta : (p 0:V)+1=Exp.exp d)')),'repunit witness')
need(all(x in pop for x in ('(hr : rankNat p v=2*r+1)','(hbin : 2*Y p v=binom (2*r) r+z*X p v)','Direct80Repunit.graph_repunit','population_lower (X p v) (Y p v) r z (d*N)')),'population hypotheses')
need(all(x in low for x in ('graph_variable_height','graph_first_main_alignment','mul_left_cancel₀','have hnr : n=r+1','lower_of_gap')),'lower witness identification')
need(all(x in up for x in ('(hpert : 2*r*3≤A0)','(hcrude : 2*r*3*power (X+1) (2*r)<A0*power X r)')),'upper open conditions')
need(all(x in rounding for x in ('(hlow :','(hup :','∃ w, 2*Y=binom (2*r) r+w*X')),'rounding assumptions')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  if directory=='ten-positive-80-projection-product-prototype' and not path.parent.name.startswith('radix-'):continue
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
