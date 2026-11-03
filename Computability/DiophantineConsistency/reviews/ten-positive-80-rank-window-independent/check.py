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
('ten-positive-80-rank-orientation-prototype','Direct80RankOrientation','attempt01','run.py','851250226a78069885a7df7265be3a18cb98b402298961d53786109aa965f3ec'),
('ten-positive-80-natural-rank-prototype','Direct80NaturalRank','attempt01','run.py','57a0cc06b1aa9d86f4907670512d3d762d1ecca68efa445d5d0b0eb3c33c6ef4'),
('ten-positive-80-scaled-growth-prototype','Direct80RankSize','ranksize-attempt02','run-ranksize.py','0412e7d295f8a8c0f705dd5479c5b83509df4d87d4d6469b8879fb71dd8359e3'),
('ten-positive-80-rank-window-prototype','Direct80RankWindow','attempt02','run.py','f41f9e9160f3fd275037c9b4d45ab0195012370996a4af06b877b0b693ec6057'),
('ten-positive-80-rank-window-prototype','Direct80RankSmall','small-attempt02','run-small.py','3e45dbe4c8ff586ee347e8331db8a3c3f3d70bc83ebdd67b85bb7e5fddc8644d'),
('ten-positive-80-rank-equality-prototype','Direct80RankEquality','attempt01','run.py','50e69b71bf026cd9a9aa853a0f963bbf7ef6ab24d316e4344d88064bc4163a0f'),
('ten-positive-80-transport-model-prototype','Direct80TransportModel','attempt01','run.py','69e42e0e58af671d9d4788a85dd867c55e6b6260058d66a28037b753b0cd14b7'),
('ten-positive-80-rank-exact-prototype','Direct80RankExact','attempt04','run.py','4efe19b01f64dde2de7feb863964bd779af1c2da2777d6075a6c40a8c62f5259')]

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
need(imports['Direct80RankSize:Direct80GraphIndex']['path']=='/tmp/tenpositive-80graphindex-vb3yq5ei/Direct80GraphIndex.olean','corrected graphindex')
exact=(B/'ten-positive-80-rank-exact-prototype/Direct80RankExact.lean').read_text()
need(all(x in exact for x in ('(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hb : 0<(p 0:V))','(hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)','rankNat p v%2=1','c p v=ycoord (rankNat p v) (A p v-1)','magnitude_of_graph_rank','apply ι_injective','hsmall : ∀ rp rn : V','graph_rank_equality_of_small p v hb hv hz hsmall','graph_rank_size p v hb hv hz',"Direct80RankWindow.window p v hb hl hh hv hgap'")),'exact rank proof scope')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  if directory=='ten-positive-80-scaled-growth-prototype' and not path.parent.name.startswith('ranksize-'):continue
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
