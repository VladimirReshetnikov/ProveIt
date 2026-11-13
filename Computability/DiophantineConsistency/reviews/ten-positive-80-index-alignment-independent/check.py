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
('ten-positive-80-first-index-residue-prototype','Direct80FirstIndexResidue','attempt01','run.py','4a6180ed99062bbe7b4d6c12f108619474de4592eabacc7035df81628ff0d8b1'),
('ten-positive-80-rank-exact-prototype','Direct80RankExact','attempt04','run.py','4efe19b01f64dde2de7feb863964bd779af1c2da2777d6075a6c40a8c62f5259'),
('ten-positive-80-index-alignment-prototype','Direct80IndexAlignment','attempt02','run.py','ab6ed54af9b184e791c9be2ab5ce27a6a5a7533b2566578564864b5f84cb6f80'),
('ten-positive-80-scaled-growth-prototype','Direct80Size','size-attempt03','run-size-v2.py','518f4241992a12e83cd61d83065221d7738e2cffa51e22249edbb0fbb3ff7c64'),
('ten-positive-80-scaled-growth-prototype','Direct80GrowthWitness','witness-attempt01','run-witness.py','e0ac4142b8bd155984bd8219782ec88a4d3587255d4ab066c5af29b26f3d1d6b'),
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
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
need(imports['Direct80IndexAlignment:DiophantineConsistency.ArithmeticPellFirstIndex']['path']=='/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticPellFirstIndex.olean','selected first-index provider')
source=(B/'ten-positive-80-index-alignment-prototype/Direct80IndexAlignment.lean').read_text()
need(all(x in source for x in ('(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hbeta : ∃u : V, (p 0:V)=2*u+1)','graph_first_index_residue p v hb hl hh hv hz hbeta','graph_rank_exact p v hb hl hh hv hz','base_mono (A0-1) B hbase n','have hnR : n<R','have hRplusM : R+1<M','have hquot : (2*n)/M=0','div_add_mod (2*n) M','2*n=rankNat p v+1')),'alignment source scope')
base=D/'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean'
need(h(base)=='8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce','base_mono source pin')
text=base.read_text();body=text[text.index('theorem base_mono'):text.index('theorem y_six')]
need('sigma1_succ_induction' in body and not re.search(r'\b(?:half_index|first_main_indices)\b',body),'base_mono source independence')
growth=(B/'ten-positive-80-scaled-growth-prototype/Direct80PowerBound.lean').read_text()
need(all(x in growth for x in ('(hbeta15 : (15:V)≤(p 0:V))','(hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hbetaodd : ∃u : V, (p 0:V)=2*u+1)','graph_first_main_alignment p v hb hl hh hv hz hbetaodd','graph_rank_exact p v hb hl hh hv hz','growth_of_witnesses p v n (rankNat p v) hb hv hX hn3 hrel.symm hny hc')),'power bound scope')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  if directory=='ten-positive-80-scaled-growth-prototype' and not path.parent.name.startswith(('power-','witness-','size-')):continue
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
