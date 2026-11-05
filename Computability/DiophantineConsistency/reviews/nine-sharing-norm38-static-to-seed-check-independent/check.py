#!/usr/bin/env python3
"""Audit static-to-seed source and immediate slot-provider routes; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-static-to-seed-check';F=D/'research/nine-sharing-norm38-forward-bridge-draft';B=D/'research/nine-sharing-norm38-slots-batched-retry01';E=D/'research/nine-sharing-norm38-each-slot-retry01';I=D/'research/nine-sharing-norm38-forward-prefix-check';BT=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105');ET=Path('/tmp/nine-sharing-norm38-each-slot-retry01-20261105');IT=Path('/tmp/nine-sharing-norm38-forward-prefix-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','3e90ef85260fadd1b09080afb5058562708b9d617cce6ba8f2202981bbd32c82'),(P/'source-manifest.json','a47bdf954ba6520400957a10e71f9c4185f0535499fdf183e54c310146c6ca5d'),(P/'src/DiophantineConsistency/Norm38StaticToSeed.lean','b7dafd1b3d9460ab2385efb8a6fae3d597be258139f98bc29d44e35d4a15a60f'),(F/'Norm38Forward.lean','70dad9e40dd83aaca364972a1b84ba62f40594aeb5ad3b62b992e66078821837'),(B/'attempt01/state.json','5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'),(E/'attempt01/state.json','8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70'),(I/'attempt01/state.json','71326dc89477d47cca893654dca94000877096b87a28ffd1086649677aa52d71')]:need(sha(p)==h,'pin '+str(p))
s=(P/'src/DiophantineConsistency/Norm38StaticToSeed.lean').read_text();orig=(F/'Norm38Forward.lean').read_text();m=re.search(r'/-- Candidate reverse use.*?(?=\n/-- Conditional forward bridge)',orig,re.S);need(m and m.group().rstrip() in s and len(re.findall(r'^theorem ',s,re.M))==1,'exact theorem copy')
manifest=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(manifest)==1 and manifest[0]['source_sha256']==sha(root/manifest[0]['source']) and manifest[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M) and len(manifest[0]['imports'])==11,'manifest')
b=json.loads((B/'attempt01/state.json').read_text());e=json.loads((E/'attempt01/state.json').read_text());i=json.loads((I/'attempt01/state.json').read_text());need(b['status']=='FAILED' and len(b['rows'])==12 and b['rows'][-1]['module']=='Norm38SlotsAssembly' and b['rows'][-1]['compile']['stop_reason']=='timeout' and e['status']==i['status']=='PASS' and len(e['rows'])==len(i['rows'])==1,'producer state')
producers=[(BT,B/'attempt01',r) for r in b['rows'][1:11]]+[(ET,E/'attempt01',e['rows'][0]),(IT,I/'attempt01',i['rows'][0])];guards=0
for temp,records,row in producers:
 n=row['module'];need(row['deps']['exit']==row['compile']['exit']==0 and all(row[k]['stop_reason'] is None and not row[k]['monitor_errors'] and not row[k]['observed_descendant_pids'] for k in ('deps','compile')),'producer exit '+n);need(sha(temp/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(temp/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'producer source/object '+n)
 for k in ('deps','compile'):need(sha(temp/(n+'-'+k+'.txt'))==sha(records/(n+'-'+k+'.txt'))==row[k]['log_sha256'],'producer log '+n+k)
 for path,v in row['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 if temp!=IT:
  link=IT/'lib/DiophantineConsistency'/(n+'.olean');need(link.is_symlink() and link.resolve()==(temp/'lib/DiophantineConsistency'/(n+'.olean')).resolve(),'overlay producer '+n)
for path,target in i['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
need(not os.path.lexists(IT/'lib/DiophantineConsistency/Norm38StaticToSeed.olean'),'target collision');r=(P/'run.py').read_text();need("producer['rows'][:11]" in r and "tuple('Norm38Slots%02d'%i for i in range(10))" in r and "each['status']=='PASS'" in r and "guard(deps)==row['direct_guard']" in r,'runner routing');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','producers':len(producers),'direct_guard_slots':guards,'overlay_links':len(i['overlay_links']),'preflight_exit':q.returncode,'scope':'Exact forward-draft theorem and recorded producer point checks only; no Lean or source equivalence.'},sort_keys=True,indent=2))
