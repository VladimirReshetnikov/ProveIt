#!/usr/bin/env python3
"""Audit 80-row index/residue/join packets and source-level noncircularity."""
import ast,json,os,re,sys
from hashlib import sha256
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research';PRIOR=B/'ordinary12-direct90-ipra-join/observations/attempt03/result.json'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');HALF=D/'Lean/DiophantineConsistency/ArithmeticPellHalfIndex.lean'
ENTRIES=[
 ('ten-positive-80-folding-prototype','Direct80Indices','attempt03','b3d6363f801ca4b9c22991b3af85f90ae14e1ef452909abd84fcf71322975e66','23a4ee7715f9d09497b449393fb5dcfd8ae6280dc1a3f46397826a321f24e49d','c4c58d9e581fd7c8e9be5a0f8fe43a7b8b0b83b0d121b405145973eef2589b9f'),
 ('ten-positive-80-residue-prototype','Direct80Residue','attempt03','31ccc63ed05b9bc84469880e8c6906ec692e2205e26ff75ba100dc715a737c44','89439c2c076fa9b652dce331652e13bdb6ad3a896cadf82a4d445dbb4288ccf4','c7aa873569b95ab818fe178f45f17b55e61b6d06dfae1eb2a482b2722d2845cf'),
 ('ten-positive-80-residue-binding-prototype','Direct80ResidueBinding','attempt02','4472d8e4cf0bda81c9db4a5cea4767beaae237900c1ef820a33e6058f11e019d','59abd5fea088f3d884d83c23d23b5086227780c4a2fa6fce0daea2a518650411','f63a86355ef79983be8adb911dae42fc966ac6a298be54ce42b18baf6f7fa1ea'),
 ('ten-positive-80-folding-joined-prototype','Direct80Joined','attempt01','e18f08d8090b79ffb53695ee3e35a1b9002d088e8110f3e06518d7179929dc50','2caa748fef16dab60c71d492f40f59dcf402bac44b0ab4907cfe742c957cd081','b21916c603b5e4aa083048017c5d089f75d9fb40f7dd3163aa6bea233709f094'),
 ('ten-positive-80-folding-consequences-prototype','Direct80Consequences','attempt02','18586777cbbb54a6baca648f6cc890425bca9978578aa72a725f773c4f9fa3ab','c94ec3204581fd951c3380b01d5a7643b07c18d530712898378ccac17e1763ac','f2c1616ade584919ef7b497f453b26d39c1c98eacfb5ddcf936be0e4ce874ef4')]
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
need(sha(PRIOR)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','prior 90 receipt')
old=json.loads(PRIOR.read_text());need(old['status']=='PASS','prior join');inputs={};direct={};outputs={};samples=0
for directory,module,attempt,source_pin,obj_pin,terminal_pin in ENTRIES:
 root=B/directory;source=root/(module+'.lean');runner=root/'run.py';obs=root/'observations'/attempt;t=obs/'terminal.json'
 need(sha(source)==source_pin and sha(t)==terminal_pin,'source/terminal pin '+module)
 r=json.loads(t.read_text());pins=r['pins'];need(r['exit']==0 and r['reason'] is None and pins==r['after'],'author status '+module)
 need(sha(obs/'source.txt')==pins['source']==source_pin and sha(runner)==pins['runner'] and sha(LEAN)==pins['lean'],'source/runner/tool '+module)
 obj=Path(r['output_root'])/(module+'.olean');need(sha(obj)==r['object_sha256']==obj_pin,'object '+module);outputs[module]=obj_pin
 need(sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 text=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostic '+module)
 reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
 need(reports and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axioms '+module)
 pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
 for x in r['samples']:
  need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2,'resource sample');samples+=1
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean')
 need(sha(provider)==pins['direct_provider'],'direct provider pin '+module)
 tree=ast.parse(runner.read_text());assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='extra' for t in n.targets))
 extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts]
 need([sha(x) for x in extras]==pins['extra'],'predecessor pins '+module)
 roots=[Path(x) for x in r['lean_path'].split(':')]
 for name in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
  rel=Path(name.replace('.','/')+'.olean');selected=next((p/rel for p in roots if (p/rel).is_file()),None);need(selected is not None,'missing direct import '+name)
  if '.' in name:
   ns=next((p for p in roots if (p/name.split('.')[0]).is_dir()),None);need(ns is not None and (ns/rel).is_file(),'namespace shadow '+name)
  direct[name]={'path':str(selected),'sha256':sha(selected)};prior=old['post_headers']['project'].get(name)
  if prior:
   need(direct[name]['sha256']==prior['record']['sha256'],'prior direct import '+name);stem=str(selected)[:-len('.olean')]
   for suffix,v in prior['companions'].items():
    now=rec(stem+suffix);need((None if now is None else now['sha256'])==(None if v is None else v['sha256']),'prior companion '+name+suffix)
 inputs[str(source)]=source_pin;inputs[str(t)]=terminal_pin;inputs[str(obj)]=obj_pin
history={
 'ten-positive-80-folding-prototype':{'attempt01':(1,'81b5cff415ec1360399dec87c40638db7e0e922590145a7d5696538b55e6a33c'),'attempt02':(0,'3274576d2d5b96cd5f631748335074eb896f148ea8fc4bb7279cdf3b36a0652d')},
 'ten-positive-80-residue-prototype':{'attempt01':(1,'c9b1f2465a70ccf4a01c80ed7a89b45b2c83791310972534cd04e4c19058288c'),'attempt02':(1,'bb32b3bd0cfdcc6f49bd9da12be9b9430071a8faf7e8a8c0dc8fb3a573a0b5b2')},
 'ten-positive-80-residue-binding-prototype':{'attempt01':(0,'1a7025e519770b571e0f929c9430a3e93b66d61feee24ed93b4c4ec79bebf02f')},
 'ten-positive-80-folding-consequences-prototype':{'attempt01':(1,'21b50f7d300c21ee13602321e7a0677e81813bc86fffa600b08bddd14291e33b')}}
for directory,cases in history.items():
 for name,(code,pin) in cases.items():
  obs=B/directory/'observations'/name;t=obs/'terminal.json';need(sha(t)==pin,'historical receipt '+name);inputs[str(t)]=pin
  r=json.loads(t.read_text());text=(obs/'stdout').read_text()+(obs/'stderr').read_text()
  need(r['exit']==code and sha(obs/'source.txt')==r['pins']['source'] and sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256'],'historical output '+name)
  need(('error' in text) if code else ('warning:' in text),'expected rejected diagnostic '+name)
indices=(B/ENTRIES[0][0]/'Direct80Indices.lean').read_text();residue=(B/ENTRIES[1][0]/'Direct80Residue.lean').read_text();binding=(B/ENTRIES[2][0]/'Direct80ResidueBinding.lean').read_text();joined=(B/ENTRIES[3][0]/'Direct80Joined.lean').read_text();consequence=(B/ENTRIES[4][0]/'Direct80Consequences.lean').read_text()
for text in (indices,residue,binding,joined,consequence):need(not re.search(r'\bhalf_index\b|\bhmain\b',text),'circular call or main-norm premise')
need('graph_adjacent p v hb hv hz' in joined and 'hV,hZ,hZeq,haux' in joined and 'graph_signed_residue p v V0 hV' in joined,'same V0 graph-square binding')
need('SignMod F V0 (c p v)' in joined and 'SignMod F V0 (ycoord (2*h+1)' in joined,'same V0 congruences')
need('rw [hV0]' in joined and 'quotient_mod_norm (A0-1) J F h hJ2 hF hstrongnorm' in joined,'odd quotient transfer')
need('have hstrong : F*F=1+D*I*I' in joined and 'have hstrongnorm : J*J+ArithmeticPellRecurrence.delta (A0-1)' in joined,'derived strong norm')
need('sign_trans hF (sign_symm hgc) hgu' in consequence and 'c p v≤I' in consequence,'same-witness consequence')
q=HALF.read_text().split('theorem quotient_mod_norm',1)[1].split('theorem quotient_mod_divisor',1)[0]
need('(hn : I*I+delta a=delta a*f*f)' in q and not re.search(r'\bhalf_index\b|\bhmain\b',q),'quotient theorem source dependency')
need(HALF.read_text().index('theorem quotient_mod_norm')<HALF.read_text().index('theorem half_index'),'half_index ordering')
half=direct['DiophantineConsistency.ArithmeticPellHalfIndex'];need(half['sha256']=='6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7','half-index provider')
for path,digest in inputs.items():need(sha(path)==digest,'input changed '+path)
for name,row in direct.items():need(sha(row['path'])==row['sha256'],'direct input changed '+name)
print(json.dumps({'status':'PASS','accepted_modules':outputs,'direct_imports':direct,'earlier_attempts':sum(map(len,history.values())),
 'resource_samples':samples,'half_index_invoked_in_checked_sources':False,'same_V0_graph_residue_and_odd_transfer':True,
 'scope':'source-level noncircularity and receipt/provider audit; no Lean replay or full historical source-object ancestry'},indent=2,sort_keys=True))
