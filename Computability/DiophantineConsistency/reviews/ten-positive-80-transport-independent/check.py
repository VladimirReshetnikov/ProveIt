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
('ten-positive-80-carrier-identity-prototype','Direct80CarrierIdentity','attempt02','run.py','19b9ab8ac4a357107ac7a65277daac0e075f63af4c647348097a0568108938d3'),
('ten-positive-transport-order-prototype','TransportOrder','attempt03','run.py','c5b2d774ac1528923f0f2ac8b62844838e4f4962bbb1708e9085400e969b5cd2'),
('ten-positive-carrier-transport-prototype','CarrierTransport','attempt03','run.py','ab4cc5151aa3d486b7a608bb77f22c1a81fee7fe7ac91a3e0d79fae91813139e'),
('ten-positive-80-transport-conditional-prototype','Direct80TransportConditional','attempt03','run.py','dcd524bc233ad7001e3adc5cd32f7f6bdbb1dca304355829e8768786899945a0'),
('ten-positive-offset-bound-prototype','OffsetBound','attempt01','run.py','50647d884710eff4cb0cfcbed3b35892b5e58b4b1cb946a2b44e8a811388006d'),
('ten-positive-80-offset-bound-prototype','Direct80OffsetBound','attempt03','run.py','d1400381f2c5e2b3b37f8b0d76564814a4eddac28c6e43dfd9f85d8dc845da39'),
('ten-positive-80-transport-mask-prototype','Direct80TransportMask','attempt02','run.py','227e52be3bbbf598092dbb87e90cd57c378e2e1b7115113d124a15194d1d5e60'),
('ten-positive-80-carrier-estimate-prototype','Direct80CarrierEstimate','attempt01','run.py','7423874a56f0b22da10c7182a58bce111e8391973b86e225681058491ffe9493'),
('ten-positive-80-carrier-estimate-prototype','CarrierSizes','sizes-attempt01','run-sizes.py','e495033b14288abf24c4106d08892103fa5ac73c13e05d8b22ce45f7a53bb094'),
('ten-positive-80-carrier-estimate-prototype','Direct80GraphCarrierBound','graph-attempt04','run-graph-v2.py','e229bbcee593496ba173ec33f7b663373c14c49c8a7db7d95d022d58332f22e7'),
('ten-positive-80-transport-model-prototype','Direct80TransportModel','attempt01','run.py','69e42e0e58af671d9d4788a85dd867c55e6b6260058d66a28037b753b0cd14b7')]
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
need(imports['Direct80GraphCarrierBound:Direct80CAboveX']['path']=='/tmp/tenpositive-80cabovex-t_50a0_0/Direct80CAboveX.olean','corrected c>X')
need(imports['Direct80TransportConditional:Direct80Kpos']['path']=='/tmp/tenpositive-80kpos-fd05z4qh/Direct80Kpos.olean','corrected Kpos')
S=lambda d,m:(B/d/(m+'.lean')).read_text()
final=S('ten-positive-80-transport-model-prototype','Direct80TransportModel');carrier=S('ten-positive-80-carrier-estimate-prototype','Direct80GraphCarrierBound')
need(all(x in final for x in ('(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (integerPorts p)).output v)','graph_carrier_bound p v hb hv hz','hZsq','hZeq','hbound','hVsq','mul_eq_zero.mp hfactor','graph_offset_bound p v hb hv','positive_mask_of_nonnegative_transport')),'model composition')
need(all(x in carrier for x in ('graph_adjacent p v hb hv hz','graph_c_above_x p v hb hv hz','CarrierSizes.sufficient','graph_signed_residue p v V0 hVs','adjacent_carrier_bound','hVs,hZs,hZeq,hbound')),'graph carrier tuple')
# Retain a read-only inventory of every terminal receipt in these producer directories.
history={}
for directory in sorted({e[0] for e in E}):
 for path in sorted((B/directory/'observations').glob('*/terminal.json')):
  r=json.loads(path.read_text());o=path.parent
  need(h(o/'source.txt')==r['pins']['source'] and h(o/'stdout')==r['stdout_sha256'] and h(o/'stderr')==r['stderr_sha256'],'historical artifacts '+str(path))
  history[str(path.relative_to(D))]={'terminal':h(path),'exit':r['exit'],'reason':r['reason'],'output':r['object_sha256'],'diagnostics':bool(re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',(o/'stdout').read_text()+(o/'stderr').read_text()))}
print(json.dumps({'status':'PASS','modules':out,'imports':imports,'resource_samples':samples,'historical_receipts':history,'scope':'selected receipts and direct imports, no Lean replay or full historical ancestry'},indent=2,sort_keys=True))
