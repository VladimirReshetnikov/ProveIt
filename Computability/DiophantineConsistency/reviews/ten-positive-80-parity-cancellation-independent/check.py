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
('ten-positive-80-rank-parity-prototype','Direct80GraphParity','graph-attempt01','run-graph.py','a31592c6c279d74649a74b2d8f78cafcbe78433f03c71f3900afcb95540d6521'),
('ten-positive-80-rank-parity-prototype','Direct80FixedParity','fixed-attempt01','run-fixed.py','17a1a0be1b47c8da979218b9a0cbb562544f2837d3402f954abe43c2c7c6a0bd'),
('ten-positive-80-carrier-divisibility-prototype','Direct80CarrierDivisibility','attempt02','run.py','859b41d843dbf4f3e040d95baae858bb43824d5ede6cfc6d80f6d5544335fd49'),
('ten-positive-80-carrier-cancel-h-prototype','Direct80CarrierCancelH','attempt02','run.py','3ea5ff3a725781b83020b954fe4d7df3e9c08f8a5c23c47adc21db2139725932'),
('ten-positive-signed-bezout-prototype','SignedBezout','attempt03','run.py','88264c9f1dea13765bd8614699ec573496cc6c5faf16ee22c8446a922715c6bc'),
('ten-positive-80-offset-divisibility-prototype','Direct80OffsetDivisibility','attempt03','run.py','ca455d36e602a77c06f43fd0518d5356673753030b4143f1c125294884827a0b'),
('ten-positive-80-first-index-congruence-prototype','Direct80FirstIndexCongruence','attempt02','run.py','cedf8aac9456dd9747bb1e409681f85fe435180d0fd06bf90cadaea9dfd6d31e'),
('ten-positive-80-first-index-residue-prototype','Direct80FirstIndexResidue','attempt01','run.py','4a6180ed99062bbe7b4d6c12f108619474de4592eabacc7035df81628ff0d8b1')]

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
# Three accepted parity/unit/beta proofs use staged author receipts.
P=B/'ten-positive-80-rank-parity-prototype'
for attempt,module,runner,pin in [('parity-attempt01','Direct80Parity','run.py','44295d34447ae9d2916ab79900a9d16b03646c1a1b7109e1b15eef8945877ff6'),('coprime-attempt02','Direct80Coprime','run-coprime.py','65dd96f13406c0ad6fb102bbbe67af1ec6c0662cf4cb6e96934808f874249759'),('betaodd-attempt02','Direct80FixedBetaOdd','run-betaodd.py','e34a2be3755a6bf4753c3909034b1f1f37171db373b2c58243ba8fdd0b80cb48')]:
 o=P/'observations'/attempt;t=o/'result.json';need(h(t)==pin,'stage receipt '+module);j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='PASS' and len(j['stages'])==1 and j['stages'][0]==st and st['exit']==0 and st['reason'] is None,'stage status '+module)
 src=P/(module+'.lean');need(h(src)==h(o/'stage-01.source.lean')==st['source_sha256']==j['sources'][module] and h(P/runner)==j['runner_sha256'],'stage source/runner '+module)
 need(h(st['command'][-1])==st['object_sha256'],'stage object '+module)
 need(h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'] and not (o/'stage-01.stderr').read_bytes(),'stage logs '+module)
 txt=(o/'stage-01.stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'stage diagnostics')
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'stage axioms')
 for path,digest in j['predecessors'].items():need(h(path)==digest,'stage predecessor')
 pre=st['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'stage preflight')
 for x in st['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'stage samples');samples+=1
 roots=[Path(x) for x in j['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');selected=next((r/rel for r in roots if (r/rel).is_file()),None);need(selected is not None,'stage missing import '+name)
  if '.' in name:
   ns=next((r for r in roots if (r/name.split('.')[0]).is_dir()),None);need(ns and (ns/rel).is_file(),'stage shadow '+name)
  imports[module+':'+name]={'path':str(selected),'sha256':h(selected)}
 out[module]={'source':st['source_sha256'],'object':st['object_sha256'],'path':st['command'][-1],'terminal':pin}
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
for attempt,pin in [('betaodd-attempt01','151618371b9b424f383d7aeda1dbfdc3b4378ca6615a53ba6049db18794b7b89'),('coprime-attempt01','64f093844d4fafb4234e97b265d53ab30c17b8e86d4cfcc461011d8bcea87ee1')]:
 o=P/'observations'/attempt;t=o/'result.json';need(h(t)==pin,'failed staged receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='FAILED' and st['exit']!=0 and h(o/'stage-01.source.lean')==st['source_sha256'] and h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'],'failed staged artifacts')
 history[str(t.relative_to(D))]={'terminal':pin,'exit':st['exit'],'output':st['object_sha256'],'diagnostics':True}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
