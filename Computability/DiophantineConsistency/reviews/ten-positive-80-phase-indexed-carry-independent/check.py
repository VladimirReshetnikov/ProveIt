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
('ten-positive-80-fixed-digits-prototype','Direct80FixedDigits','fixeddigits-attempt01','run.py','0afcb88ede0ad67f9f619aa7ce118db60c51e45b0e6224efb445e7884fa17fa4'),
('ten-positive-80-rank-phase-prototype','Direct80RankPhase','fixeddigits-attempt05','run.py','9f9524936110dd60cbfe593e9768604efbaf96dd9df934f889b546454f2e30f8'),
('ten-positive-80-fixed-congruence-prototype','Direct80FixedCongruence','fixedcongruence-attempt02','run.py','ded12bfe34489706f371fb7adaac5c9c602ddc286e32a5dc509baad43282829b'),
('ten-positive-80-band-temporal-prototype','Direct80BandTemporal','bandtemporal-attempt01','run.py','bd8c2e9e212c3055d2a069eaed2390a66d9a1645eb38dbcf4bc6ba6b0f99277d'),
('ten-positive-80-indexed-carry-prototype','Direct80IndexedCarry','indexedcarry-attempt01','run.py','cfcc203ab2e014571dba17db8a03f1a1ec00c4089e53bea803cfd90b5904049d')]

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
  if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='extra' and n.value.func.attr=='extend':extras.extend(Path(ast.literal_eval(x.args[0])) for x in n.value.args[0].elts)
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
for key,row in imports.items():
 module=key.split(':',1)[0];need(row['path'] in out[module]['extra_paths'],'un-pinned direct import '+key)
phase=(B/'ten-positive-80-rank-phase-prototype/Direct80RankPhase.lean').read_text();cong=(B/'ten-positive-80-fixed-congruence-prototype/Direct80FixedCongruence.lean').read_text();band=(B/'ten-positive-80-band-temporal-prototype/Direct80BandTemporal.lean').read_text();carry=(B/'ten-positive-80-indexed-carry-prototype/Direct80IndexedCarry.lean').read_text()
need(all(x in phase for x in ('(hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)','rankNat p v % 4 = 3','Direct80FixedDigits.graph_fixed_digits','CompactConcreteMask.model_origin','model_residues 4','have hJodd','linear_combination -hFα+hJodd')),'phase proof')
need(all(x in cong for x in ("have hNN : N'=N","exp_inj (hq'.symm.trans hq)",'v 5=Exp.exp (rankNat p v-(67*8807)*N)','((p 1:V)+v 5)*Cnat p v','graph_radix_alignment')),'congruence witness')
need(all(x in band for x in ('(hK : (p 1:V)=kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel)','graph_fixed_congruence','(Cnat p v) (v 5) (v 1)','graph_temporal_word','v 5=Exp.exp (rankNat p v-(67*8807)*N)')),'band residual mapping')
need(all(x in carry for x in ('(hp1 : p 1=paramKernel rho)','symbolic_kernel_band_cast','graph_band_temporal p v position hp0 hp2 hp3 hv hz hK','CompactTwoBandCarry.carry_input','v 5=Exp.exp (rankNat p v-(67*8807)*N)')),'indexed carry')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
