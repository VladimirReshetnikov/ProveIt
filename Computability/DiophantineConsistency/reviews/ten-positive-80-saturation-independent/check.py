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
('ten-positive-80-population-model-prototype','Direct80PopulationModel','populationmodel-attempt01','run.py','d3f8b1b8d21a972b6e3043b61d7e9125465c2574411d2d97e69155806ba547d8'),
('ten-positive-80-symbolic-port-bounds-prototype','Direct80SymbolicPortBounds','attempt01','run.py','926f002971d186ebfc03bbcba969119793a47dd83bb472aa7efc2742edb40383'),
('ten-positive-80-saturation-prototype','Direct80Saturation','saturation-attempt02','run.py','a57cf0594d04aac4cbbac3877d3b3f2558a9565e044d512df60cad947189207d'),
('ten-positive-80-fixed-saturation-prototype','Direct80FixedSaturation','fixedsaturation-attempt03','run-v2.py','a74ea607fe5570e586b57d0a9104db35850ae1e42eeb15c66fe283e137b3020c')]

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
  if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='extra':
   if isinstance(n.value,ast.List):extras.extend(Path(ast.literal_eval(x.args[0])) for x in n.value.elts)
   elif isinstance(n.value,ast.ListComp):
    names=ast.literal_eval(n.value.generators[0].iter);need(names==['CompactFixedBeta','CompactSymbolicPorts','CompactLowExact','CompactLowEven','CompactHighResidue','CompactHighPopulation','CompactConcreteMask'],'unexpected compact provider list');extras.extend(Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency')/(name+'.olean') for name in names)
   else:raise RuntimeError('unexpected extra '+module)
  if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='extra' and n.value.func.attr=='append':extras.append(Path(ast.literal_eval(n.value.args[0].args[0])))
 need([h(x) for x in extras]==p['extra'],'predecessors '+module);out[module]['extra_paths']=[str(x) for x in extras]
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
fixedroot=B/'ten-positive-80-fixed-saturation-prototype';old=fixedroot/'observations/fixedsaturation-attempt02/terminal.json';need(h(old)=='558b65cc2807a4d20226a8aea2ad577e63a67d6266ad111eae39ef233af3cd23','earlier fixed receipt');oldj=json.loads(old.read_text());newj=json.loads((fixedroot/'observations/fixedsaturation-attempt03/terminal.json').read_text());need(oldj['exit']==0 and oldj['pins']['source']==newj['pins']['source'] and oldj['object_sha256']==newj['object_sha256'] and h(Path(oldj['output_root'])/'Direct80FixedSaturation.olean')==oldj['object_sha256'],'fixed object match')
for name in ['CompactLowExact','CompactLowEven','CompactHighResidue']:
 rel='Direct80FixedSaturation:DiophantineConsistency.'+name;need(rel in imports,'missing selected compact import '+name)
for name in ['CompactFixedBeta','CompactSymbolicPorts','CompactLowExact','CompactLowEven','CompactHighResidue','CompactHighPopulation','CompactConcreteMask']:
 obj='/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/'+name+'.olean'
 need(obj in out['Direct80FixedSaturation']['extra_paths'],'missing compact pin '+name)
for name in ['CompactLowExact','CompactLowEven','CompactHighResidue']:
 need(imports['Direct80FixedSaturation:DiophantineConsistency.'+name]['path']=='/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/'+name+'.olean','compact import resolution '+name)
f=(fixedroot/'Direct80FixedSaturation.lean').read_text();q=(B/'ten-positive-80-saturation-prototype/Direct80Saturation.lean').read_text()
need(all(x in f for x in ('(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)','fixed_bounds (V:=V) p hp0 hp2 hp3','CompactLowExact.model_population','CompactHighPopulation.model_population','CompactLowEven.low_even','CompactHighResidue.model_mod_eight','CompactFixedBeta.bounds (v 0) (hv 0)','Direct80Saturation.graph_saturation')),'fixed compact scope')
need(all(x in q for x in ('(hport : (p 3:V)=HP+(p 0:V))','(hMC : (p 2:V)<Exp.exp d) (hHP : HP<Exp.exp d)','(hMC2 : (p 2:V)%2=0) (hHP8 : HP%8=4)','(hsum : population (p 2:V)+population HP=d) (hHPJ : 1≤HP*v 0)','obtain ⟨N,hN,hJ,hpop⟩','repeated_mask_population d N','ArithmeticSaturation.saturation (d*N)')),'conditional mask scope')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
