#!/usr/bin/env python3
"""Read-only audit of 80 main-norm, signed-rank and growth packets."""
import ast,json,os,re,sys
from pathlib import Path
from hashlib import sha256
D=Path(__file__).resolve().parents[2];B=D/'research'; L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
if sys.flags.optimize:raise RuntimeError('optimized Python')
def h(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(v,msg):
 if not v:raise RuntimeError(msg)
E=[
('ten-positive-80-main-norm-prototype','Direct80MainNorm','attempt01','run.py','30a6b862f8e5ca123c9bee2ef1aae17aea471183d17ab3dc737e419a1ab2101a'),
('ten-positive-signed-rank-prototype','SignedRank','attempt01','run.py','be592a58ccaf832504ac6608f35e8777f865dd19cf7e549d187dddc8b5ee5b5e'),
('ten-positive-signed-rank-index-prototype','SignedRankIndex','attempt01','run.py','f855817d14409adc64d7dc9e713bea95e92db94d8f4d805fcdd9c56b2b24b8cd'),
('ten-positive-80-rank-index-prototype','Direct80RankIndex','attempt01','run.py','751ab7d3d06ee650856a2ad048a10be9fdcce198d2775d317d7977aa989e5b92'),
('pell-rank-reduction-prototype','PellRankReduction','attempt02','run.py','db7b9f23f17943479777ebf2d92e2f95d399460f8748cc701dd9b9cdad2ca7c1'),
('ten-positive-80-rank-main-prototype','Direct80RankMain','attempt01','run.py','a5c0f50688dfb606a29adf06b9ede273ac626232ef02746ca92b853dffd2950b'),
('ten-positive-80-rank-equality-prototype','Direct80RankEquality','attempt01','run.py','50e69b71bf026cd9a9aa853a0f963bbf7ef6ab24d316e4344d88064bc4163a0f'),
('ten-positive-80-scaled-growth-prototype','Direct80GraphGrowth','attempt01','run-graph.py','8b1be74e4e96aa5e3769609efe2bf86caea9ba0b416e3c48e758c85e8ba89035'),
('ten-positive-80-scaled-growth-prototype','Direct80GraphIndex','graphindex-attempt01','run-graphindex.py','e71e7a1d3fb507b2c058fcea471751d5df8ee17c5c946b3771ee743da650c37c')]
modules={};imports={};samples=0
for directory,module,attempt,runner,pin in E:
 root=B/directory;obs=root/'observations'/attempt;t=obs/'terminal.json';src=root/(module+'.lean');run=root/runner
 need(h(t)==pin,'terminal '+module);j=json.loads(t.read_text());p=j['pins'];need(j['exit']==0 and j['reason'] is None and p==j['after'],'status '+module)
 need(h(src)==h(obs/'source.txt')==p['source'] and h(root/'run.py')==p['runner'] and h(L)==p['lean'],'pins '+module)
 need(h(obs/'stdout')==j['stdout_sha256'] and h(obs/'stderr')==j['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 txt=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'diagnostics '+module)
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'axioms '+module)
 obj=Path(j['output_root'])/(module+'.olean');need(h(obj)==j['object_sha256'],'output '+module);modules[module]={'source':p['source'],'object':h(obj),'terminal':pin}
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean');need(h(provider)==p['direct_provider'],'provider '+module)
 tree=ast.parse(run.read_text());assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='extra' for x in n.targets));extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts]
 for n in tree.body:
  if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='extra':extras.extend(Path(ast.literal_eval(x.args[0])) for x in n.value.elts)
  if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='extra' and n.value.func.attr=='append':extras.append(Path(ast.literal_eval(n.value.args[0].args[0])))
 need([h(x) for x in extras]==p['extra'],'predecessors '+module)
 roots=[Path(x) for x in j['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');chosen=next((r/rel for r in roots if (r/rel).is_file()),None);need(chosen is not None,'import '+module+' '+name)
  if '.' in name:
   ns=next((r for r in roots if (r/name.split('.')[0]).is_dir()),None);need(ns and (ns/rel).is_file(),'shadow '+name)
  imports[module+':'+name]={'path':str(chosen),'sha256':h(chosen)}
 pre=j['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'preflight')
 for sample in j['samples']:
  need(sample['mem_available_kib']>=8*1024**2 and len(sample['lean'])<=2,'sample');samples+=1
# Two staged author results use a second runner format.
for attempt,module,pin in [('minus-attempt01','Direct80ScaledGrowthMinus','3104241629a7ef7284e390dacc968ab054f1d3034915fc1d8351715d2e1dfb08'),('indexone-attempt02','Direct80IndexOne','ea78aba9fba08a57ec2eb87a02e49ac854b87dcfa29b4c53b1dd18b632b49a8a')]:
 root=B/'ten-positive-80-scaled-growth-prototype';o=root/'observations'/attempt;t=o/'result.json';need(h(t)==pin,'staged receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='PASS' and len(j['stages'])==1 and j['stages'][0]==st and st['exit']==0 and st['reason'] is None,'staged status')
 runner='run-minus.py' if module=='Direct80ScaledGrowthMinus' else 'run-indexone.py';need(h(root/runner)==j['runner_sha256'],'staged runner')
 src=root/(module+'.lean');need(h(src)==h(o/'stage-01.source.lean')==st['source_sha256']==j['sources'][module],'staged source');need(h(st['command'][-1])==st['object_sha256'],'staged object')
 need(h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'] and not (o/'stage-01.stderr').read_bytes(),'staged logs');txt=(o/'stage-01.stdout').read_text();need('sorryAx' not in txt and not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt),'staged diagnostics')
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'staged axioms')
 for p,v in j['predecessors'].items():need(h(p)==v,'staged predecessor')
 need(st['preflight']['mem_available_kib']>=8*1024**2 and len(st['preflight']['lean_pids'])<2,'staged preflight')
 for x in st['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'staged sample');samples+=1
 modules[module]={'source':st['source_sha256'],'object':st['object_sha256'],'terminal':pin}
# Exact premise boundaries and key noncircular composition points.
S=lambda directory,module:(B/directory/(module+'.lean')).read_text()
main=S('ten-positive-80-main-norm-prototype','Direct80MainNorm')
red=S('pell-rank-reduction-prototype','PellRankReduction')
rank=S('ten-positive-80-rank-main-prototype','Direct80RankMain')
eq=S('ten-positive-80-rank-equality-prototype','Direct80RankEquality')
growth=S('ten-positive-80-scaled-growth-prototype','Direct80ScaledGrowthMinus')
index=S('ten-positive-80-scaled-growth-prototype','Direct80GraphIndex')
for z in (main,red,rank,eq,growth,index):need(not re.search(r'\bhalf_index\b',z),'unexpected half_index invocation')
need(all(x in main for x in ('graph_odd_ordinate p v hb hv hz','have hh := norm r (A0-1)','d*d=1+delta p v*(c p v)*(c p v)')),'main norm source')
need(all(x in red for x in ('(hmain : SignMod (xcoord n b) c (ycoord s b))','(hrank : SignMod c R s)','ordinate_divides_index','doubled_step_down')),'rank reduction scope')
need(all(x in rank for x in ('graph_main_norm p v hb hv hz','graph_rank_index p v hb hv hz',"hj hr3 hc hdiv' htarget' hRmod")),'same-witness rank assembly')
need(all(x in eq for x in ('(hsmall : ∀ rp rn : V,','2*absdiff rp rn<c p v','absdiff rp rn=r')),'unproved rank size premise')
need(all(x in growth for x in ('(hX : 16≤X) (hS : 1≤S) (hr : 2≤r)','(hck : c=k*Y+eta) (hkez : k=eta+zeta) (hz : 0<zeta)','(hc : c=ycoord (2*r+1) (S*(X+1)-1))','(hk : k=2*ycoord (r+1) (2*(X*S*S-1)+1))')),'corrected growth premises')
need('(hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v)' in index and 'Direct80IndexOne.impossible' in index,'graph index premise')
print(json.dumps({'status':'PASS','modules':modules,'direct_imports':imports,'resource_samples':samples,'scope':'read-only direct selected inputs and receipts; no Lean replay or full transitive source/object ancestry'},indent=2,sort_keys=True))
