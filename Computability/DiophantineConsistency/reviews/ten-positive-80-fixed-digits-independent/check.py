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
('ten-positive-80-fixed-saturation-prototype','Direct80FixedSaturation','fixedsaturation-attempt03','run-v2.py','a74ea607fe5570e586b57d0a9104db35850ae1e42eeb15c66fe283e137b3020c'),
('ten-positive-80-natural-transport-prototype','Direct80NaturalTransport','graphpower-attempt02','run.py','5b9d15d9a0aed355886902c07ce0f215c3c31de5a3f5e8825f0e7723e49f378a'),
('ten-positive-80-fixed-digits-prototype','Direct80FixedDigits','fixeddigits-attempt01','run.py','0afcb88ede0ad67f9f619aa7ce118db60c51e45b0e6224efb445e7884fa17fa4'),
('ten-positive-80-fixed-slots-prototype','Direct80FixedSlots','fixedslots-attempt03','run.py','a5bcc34beb421f5dad34d72fab87298a8ace3b7a624d073b0b4ed7b595c2e86f'),
('ten-positive-80-v-positive-prototype','Direct80VPositive','attempt02','run.py','7406122b2af2aaf921a868649203c94395477c3278cfa216ee67d964e456a366')]

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
   if isinstance(n.value,ast.List):
    for x in n.value.elts:
     if isinstance(x,ast.Call):extras.append(Path(ast.literal_eval(x.args[0])))
     elif isinstance(x,ast.BinOp) and isinstance(x.op,ast.Div) and isinstance(x.left,ast.Name) and x.left.id=='lib':extras.append(Path('/tmp/direct90-ipra-join-b66u_qqo/lib')/ast.literal_eval(x.right))
     else:raise RuntimeError('unexpected provider expression '+module)
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
slots=(B/'ten-positive-80-fixed-slots-prototype/Direct80FixedSlots.lean').read_text();digits=(B/'ten-positive-80-fixed-digits-prototype/Direct80FixedDigits.lean').read_text();vpos=(B/'ten-positive-80-v-positive-prototype/Direct80VPositive.lean').read_text()
old=(B/'ordinary12-ipra-bridge/compact44-position-carry-prototype/observations/attempt02/CompactPositionCarry.lean').read_text();a=old[old.index('theorem increment_digits'):old.index('/-- Per-slot no-carry')].strip();b=slots[slots.index('theorem increment_digits'):slots.index('theorem graph_fixed_slots')].strip();need(a==b and __import__('hashlib').sha256(a.encode()).hexdigest()=='ec5772c9b0278a6515abb7bf14c371cccaf2932e12591146a638ccccbc8f4ea9','reproduced increment')
need(all(x in digits for x in ('(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)','graph_fixed_saturation p v hp0 hp2 hp3 hv hz','graph_natural_transport p v h31 hl hh hv hz hodd','CompactConcreteIncrement.recipe_digits N (Cnat p v)','⟨N,t,hN,hJ,hq,hC,ht,hzero,hdigits,hnchigh⟩')),'digits scope')
need(all(x in slots for x in ('graph_fixed_saturation p v hp0 hp2 hp3 hv hz','increment_digits 8807 N (Cnat p v)','NoCarry (dig 67 (Cnat p v) j) (dig 67 (lowNat:V) (j%8807))','⟨N,hN,hJ,hq,hC,hzero,hslots,hhigh⟩')),'slot witness')
need(all(x in vpos for x in ('(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','graph_rank_exact p v hb hl hh hv hz','graph_rank_size p v hb hv hz','graph_natural_rank p v hb hv hz','one_le_of_pos','0 < (graph (integerPorts p)).v.evalRing')),'signed V scope')
for mod,name in [('Direct80FixedDigits','CompactConcreteIncrement'),('Direct80FixedSlots','CompactMixedIncrement')]:
 key=mod+':DiophantineConsistency.'+name;need(key in imports and imports[key]['path'] in out[mod]['extra_paths'],'compact direct pinned '+name)
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
