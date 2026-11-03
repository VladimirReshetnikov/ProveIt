#!/usr/bin/env python3
"""Read-only audit of selected 80-graph transport producers."""
import ast,json,re,sys,os
from pathlib import Path
from hashlib import sha256
if sys.flags.optimize:raise RuntimeError('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
E=[
('ten-positive-80-projection-pell-prototype','Direct80ProjectionPell','attempt02','run.py','cdbe0eb0e80d2c0cf2740a60defe6a2c9b3b94922af12aecb3ce2f51845046c0'),
('ten-positive-80-projection-product-prototype','Direct80GraphPower','graphpower-attempt01','run-graphpower.py','7769b721a22240d34b64b4363abae11d77d47074d863a1b860a8b97a49fd7bf6'),
('ten-positive-80-projection-product-prototype','Direct80GraphUnweighted','graphunweighted-attempt01','run-graphunweighted.py','b80f76373a4e1def9482cf722b8b45fed06f0e8aa657f52eb81b33d6eece9b08'),
('ten-positive-80-projection-product-prototype','Direct80Kappa','kappa-attempt01','run-kappa.py','11dda0c5144fc22de641edff4f722ec8a283b772f9d72d2ad6c325249aabf728'),
('ten-positive-80-offset-divisibility-prototype','Direct80OffsetDivisibility','attempt03','run.py','ca455d36e602a77c06f43fd0518d5356673753030b4143f1c125294884827a0b'),
('ten-positive-80-offset-exact-prototype','Direct80OffsetExact','attempt02','run.py','ee4ecc0be40a04f21cac7e0973a2be3999635020574b6de2ecbe7d4bb3510005'),
('ten-positive-transport-integral-prototype','TransportIntegral','attempt02','run.py','60544e712932e34ce298661a89134eeaaa51d70d08740267651bcc5ad19d8e9d'),
('ten-positive-80-transport-integral-graph-prototype','Direct80TransportIntegralGraph','graphpower-attempt01','run.py','0c86b96d21ac758773b3a90d662eadf06aee8567c91943a3bfb8570b6de4913c')]

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
# Abstract full-product height estimate has a staged author receipt.
P=B/'ten-positive-80-projection-product-prototype';o=P/'observations/unweighted-attempt01';t=o/'result.json';pin='343640bbba398a2e00e14fe89fb9409a7b49a67a28d9706d33db65dff907b429'
need(h(t)==pin,'power receipt');j=json.loads(t.read_text());st=json.loads((o/'stage-01.json').read_text());need(j['status']=='PASS' and j['stages']==[st] and st['exit']==0 and st['reason'] is None,'power status')
module='Direct80UnweightedProjection';src=P/(module+'.lean');need(h(src)==h(o/'stage-01.source.lean')==st['source_sha256']==j['sources'][module] and h(P/'run-unweighted.py')==j['runner_sha256'],'power source/runner')
need(h(st['command'][-1])==st['object_sha256'] and h(o/'stage-01.stdout')==st['stdout_sha256'] and h(o/'stage-01.stderr')==st['stderr_sha256'] and not (o/'stage-01.stderr').read_bytes(),'power object/log')
txt=(o/'stage-01.stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',txt) and 'sorryAx' not in txt,'power diagnostics')
ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",txt,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'power axioms')
for path,digest in j['predecessors'].items():need(h(path)==digest,'power predecessor')
base=B/'ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json';need(h(base)=='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f','power base receipt')
lib=Path('/tmp/qcube92-halt-5apqi7f7/lib')
def record(p):return {'sha256':h(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
union={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
need(len(union)==1291 and union==json.loads(base.read_text())['union'],'power provider union')
pre=st['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'power preflight')
for x in st['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'power sample');samples+=1
out[module]={'source':st['source_sha256'],'object':st['object_sha256'],'path':st['command'][-1],'terminal':pin}
for k,v in imports.items():
 name=k.split(':',1)[1]
 if name in out:need(v['sha256']==out[name]['object'],'producer object mismatch '+k)
u=(P/'Direct80UnweightedProjection.lean').read_text();g=(P/'Direct80GraphUnweighted.lean').read_text();kappa=(P/'Direct80Kappa.lean').read_text();integral=(B/'ten-positive-80-transport-integral-graph-prototype/Direct80TransportIntegralGraph.lean').read_text();generic=(B/'ten-positive-transport-integral-prototype/TransportIntegral.lean').read_text()
need(all(x in u for x in ('(hd : d=X+a*c+(4*a+3)*z)','(hnorm : d*d=1+(a*a+(4*a+3))*c*c)','hnormdiv')),'unweighted norm')
need(all(x in g for x in ('graph_projection_pell p v hb hl hh hv hz','graph_power p v hbeta31 hl hh hv hz hbetaodd','Direct80UnweightedProjection.unweighted','natural_dvd_of_signed H (Knat p v) hdivR')),'graph binding')
need('∃ kappa : V, 0<kappa ∧ Knat p v=Hnat p v*kappa' in kappa,'positive quotient')
need(all(x in generic for x in ('[NoZeroDivisors R]','(hm : m≠0) (hH : H≠0)','(mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hm hH)','h∣B')),'domain cancellation')
need(all(x in integral for x in ('(hbeta31 : (31:V)≤(p 0:V))','(hbetaodd : ∃u : V, (p 0:V)=2*u+1)','graph_signed_carrier p v hb hv hz','graph_unweighted p v hbeta31 hl hh hv hz hbetaodd','graph_offset_divisible p v hb hl hh hv hz hbetaodd','graph_transport_and_mask p v hb hv hz','natural_dvd_of_signed (b p v) B0 hdiv')),'graph transport composition')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
