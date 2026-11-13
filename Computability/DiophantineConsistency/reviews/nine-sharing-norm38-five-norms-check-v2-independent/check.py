#!/usr/bin/env python3
"""Review five-norm source and individually authenticated direct slot producers; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-five-norms-check-v2';O=D/'research/nine-sharing-norm38-five-norms-check';B=D/'research/nine-sharing-norm38-slots-batched-retry01';I=D/'research/nine-sharing-norm38-each-slot-retry01';BT=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105');IT=Path('/tmp/nine-sharing-norm38-each-slot-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','87a6efdd5435c7f3b82ae7d8e3fc44bbbb5d62a2a87d431389a927b1ec7bfa6d'),(P/'source-manifest.json','2d8553d1e5219573581b54247be82eb51c965913b962ec20ee4288e980a5472a'),(P/'src/DiophantineConsistency/Norm38FiveNorms.lean','659df3272bc175cad9a3a461d01c52cc3d10a6375f16c351a0e6093a28f383d2'),(B/'attempt01/state.json','5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'),(I/'attempt01/state.json','8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70')]:need(sha(p)==h,'pin '+str(p))
need(sha(P/'source-manifest.json')==sha(O/'source-manifest.json') and sha(P/'src/DiophantineConsistency/Norm38FiveNorms.lean')==sha(O/'src/DiophantineConsistency/Norm38FiveNorms.lean'),'v1 inputs')
s=(P/'src/DiophantineConsistency/Norm38FiveNorms.lean').read_text();slots=json.loads((D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json').read_text())['slots'];need([slots[i]['gate'] for i in (16,11,27,17,28)]==['N0','N1','Na','Nt','scaled_Ns'],'norm order');need('⟨sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27,\n    sub_eq_zero.mp h17, sub_eq_zero.mp h28⟩' in s,'norm projections');need('∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in s and 'InternalZero (SharingSeed38.seed p)' in s,'hypotheses')
m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==1 and m[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M) and m[0]['source_sha256']==sha(root/m[0]['source'])==sha(P/'src/DiophantineConsistency/Norm38FiveNorms.lean'),'manifest')
b=json.loads((B/'attempt01/state.json').read_text());im=json.loads((I/'attempt01/state.json').read_text());need(b['status']=='FAILED' and len(b['rows'])==12 and b['rows'][-1]['module']=='Norm38SlotsAssembly' and b['rows'][-1]['compile']['stop_reason']=='timeout','batched partial state');need(im['status']=='PASS' and len(im['rows'])==1 and im['base_state_sha256']==sha(B/'attempt01/state.json'),'immediate state');need(sha(IT/'state.json')==sha(I/'attempt01/state.json') and sha(BT/'state.json')==sha(B/'attempt01/state.json'),'temporary states')
guards=0
for parent,state_dir,r in [(IT,I/'attempt01',im['rows'][0])]+[(BT,B/'attempt01',next(r for r in b['rows'][:11] if r['module']==name)) for name in ('Norm38Slots03','Norm38Slots05','Norm38Slots09')]:
 n=r['module'];need(r['deps']['exit']==0 and r['compile']['exit']==0 and r['deps']['stop_reason'] is None and r['compile']['stop_reason'] is None and sha(parent/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(parent/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'],'producer '+n)
 for typ in ('deps','compile'):need(sha(parent/(n+'-'+typ+'.txt'))==sha(state_dir/(n+'-'+typ+'.txt'))==r[typ]['log_sha256'],'producer log '+n+typ)
 for path,v in r['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 if parent==BT:
  overlay=IT/'lib/DiophantineConsistency'/(n+'.olean');need(overlay.is_symlink() and overlay.resolve()==(BT/'lib/DiophantineConsistency'/(n+'.olean')).resolve(),'direct slot route '+n)
for path,target in im['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
r=(P/'run.py').read_text();need("for n in ('Norm38Slots03','Norm38Slots05','Norm38Slots09')" in r and "producer['rows'][:11]" in r and "overlay.resolve()==(PRODUCER/" in r and "guard(deps)==row['direct_guard']" in r,'runner checks');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','authenticated_direct_producers':4,'producer_guard_slots':guards,'immediate_overlay_links':len(im['overlay_links']),'preflight_exit':q.returncode,'scope':'Point-in-time source/producer route review; no Lean and no full model bridge.'},sort_keys=True,indent=2))
