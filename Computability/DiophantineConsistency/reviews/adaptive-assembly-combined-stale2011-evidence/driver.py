from pathlib import Path
import hashlib,json,os,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');I=Path('/tmp/adaptive13-assembly-independent-4tmj26_8');P=Path('/tmp/adaptive13-assembly-pell-mg258xlh');Q=Path('/tmp/adaptive13-assembly-prefix-d_s896gq');M=Path('/tmp/adaptive13-machine-independent-2fb2oum7');D=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');K=Path('/tmp/adaptive13-ranklower-postmerge-tjqelwlk');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
branches=[('pell',P,K/'lib'),('prefix',Q,I/'lib'),('machine',M,I/'lib')];states={};maps={};entries={};source_rows=[]
for label,p,base in branches:
 s=read(p/'state.json');assert s['status']=='PASS',(label,s['status']);states[label]=s;m={}
 for r in read(p/'providers.json'):
  q=Path(r['path']);root=D/'lib' if q.is_relative_to(D/'lib') else base if q.is_relative_to(base) else None;assert root is not None,(label,q)
  rel=str(q.relative_to(root));assert rel not in m or m[rel]==r['sha256'];m[rel]=r['sha256'];entries.setdefault(rel,(q,r['sha256']))
 for r in s['records']:
  ns=r.get('namespace','DiophantineConsistency');n=r['name'];rel=str(Path(ns)/(n+'.olean'));obj=p/'lib'/rel;src=roots[ns]/(n+'.lean');assert sha(obj)==r['object_sha256'] and sha(src)==r['source_sha256'];m[rel]=r['object_sha256'];entries.setdefault(rel,(obj,r['object_sha256']));source_rows.append({'branch':label,'namespace':ns,'name':n,'source':str(src),'source_sha256':r['source_sha256'],'object':str(obj),'object_sha256':r['object_sha256']})
 maps[label]=m
is_=read(I/'state.json');assert is_['status']=='PASS'
for r in is_['records']:
 ns='DiophantineConsistency';n=r['name'];src=roots[ns]/(n+'.lean');obj=I/'lib'/ns/(n+'.olean');assert sha(src)==r['source_sha256'] and sha(obj)==r['object_sha256'];source_rows.append({'branch':'base','namespace':ns,'name':n,'source':str(src),'source_sha256':r['source_sha256'],'object':str(obj),'object_sha256':r['object_sha256']})
pairs=[]
for a,b in [('pell','prefix'),('pell','machine'),('prefix','machine')]:
 common=maps[a].keys()&maps[b].keys();different=sorted(k for k in common if maps[a][k]!=maps[b][k]);assert not different,(a,b,different);pairs.append({'left':a,'right':b,'common':len(common),'different':different})
# Recheck each branch's independently audited project-source closure.
for label,p,_ in branches:
 audit=read(p/'audit.json')
 for row in audit['rows']:
  if label=='pell':src=roots['DiophantineConsistency']/(row['module']+'.lean');obj=Path(row['resolved_object'])
  else:
   ns,n=row['module'].split('.',1);src=roots[ns]/(n.replace('.','/')+'.lean') if ns in roots else None
   if src is None:continue
   obj=Path(row['object'])
  assert sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],(label,row['module'])
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-assembly-combined-'));lib=w/'lib';lib.mkdir();shutil.copyfile(__file__,w/'driver.py');providers=[]
for rel,(source,h) in sorted(entries.items()):
 assert sha(source)==h,(rel,source);dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(source.resolve());providers.append({'relative':rel,'path':str(source),'resolved':str(source.resolve()),'sha256':h})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for x in providers:assert sha(x['path'])==x['sha256']
for x in source_rows:assert sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256']
state={'status':'PASS','private':str(w),'scope':'composition of three independently replayed current-source prerequisite branches; shared objects compared and selected objects rehashed; package and cache boundaries inherited','base':{'path':str(I),'state_sha256':sha(I/'state.json'),'audit_sha256':sha(I/'audit.json')},'branches':{label:{'path':str(p),'state_sha256':sha(p/'state.json'),'audit_sha256':sha(p/'audit.json')} for label,p,_ in branches},'pairs':pairs,'records':source_rows,'providers_sha256':sha(w/'providers.json'),'boundary':read(I/'state.json')['boundary']};(w/'state.json').write_text(json.dumps(state,indent=2)+'\n');print('PASS',w,'objects',len(providers),'pairs',pairs,flush=True)
