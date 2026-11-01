#!/usr/bin/env python3
"""Frozen 86-operation classical endpoint on an authenticated 848+73 classical parent."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile,time,tomllib
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
M=json.loads((PACKET/'manifest.json').read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
executed=os.environ.get('PRA14_JOIN_EXEC_SHA256');launcher=os.environ.get('PRA14_JOIN_LAUNCHER_SHA256')
if not executed or not launcher:raise SystemExit('use run.py to authenticate executed driver bytes')
ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);args=ap.parse_args();C=args.parent.resolve();CS=C/'state.json'
w=Path(tempfile.mkdtemp(prefix='pra86-classical-join-'));src=w/'src';lib=w/'lib';logs=w/'logs';logs.mkdir();lib.mkdir();(src/'DiophantineConsistency').mkdir(parents=True)
s={'status':'RUNNING','phase':'initialization','root':str(w),'classical_parent':str(C),'manifest_sha256':sha(PACKET/'manifest.json'),'driver_sha256':executed,'launcher_sha256':launcher,'records':[],'scope':M['scope']}
def save():
 q=w/'state.tmp';q.write_text(json.dumps(s,indent=2)+'\n');q.replace(w/'state.json')
def need(p,h,why):
 if not p.is_file() or sha(p)!=h:raise RuntimeError(why+': '+str(p))
save();print('ROOT',w,flush=True)
try:
 need(PACKET/'replay.py',executed,'driver');need(PACKET/'run.py',launcher,'launcher')
 refs={}
 for key in ['parent_snapshot','parent_audit','classical_join_manifest']:
  keypath=key+'_manifest' if key=='parent_snapshot' else key
  keysha=key+'_sha256' if key!='parent_snapshot' else 'parent_snapshot_sha256'
  p=(PACKET.parent/M[keypath]).resolve();need(p,M[keysha],key);refs[key]=p
 expected=json.loads(refs['parent_audit'].read_text())['graph'];snap=json.loads(refs['parent_snapshot'].read_text());tree=Path(snap['root'])/'tree';jm=json.loads(refs['classical_join_manifest'].read_text())
 cs=json.loads(CS.read_text());assert cs['status']=='PASS' and len(cs['records'])==len(jm['order'])==75,'classical parent must be passed complete 75-module join'
 if cs['manifest_sha256']!=M['classical_join_manifest_sha256']:raise RuntimeError('classical parent used another join manifest')
 B=Path(cs['parent']);bsfile=B/'state.json';bs=json.loads(bsfile.read_text());assert bs['status']=='PASS' and len(bs['records'])==848,'underlying 848 parent must PASS';g=bs['graph']
 for k in ['sources','edges','order','source_hashes','external_paths','external_hashes','external_companions','anchors']:
  if g[k]!=expected[k]:raise RuntimeError('848 source graph differs: '+k)
 if any(not r.get('verified') for r in bs['records']):raise RuntimeError('unverified 848 parent record')
 br={r['module']:r for r in bs['records']};cr={r['module']:r for r in cs['records']};assert set(br)==set(g['order']) and set(cr)==set(jm['order'])
 if set(M['order']) & (set(br)|set(cr)) or len(set(M['order']))!=len(M['order']):raise RuntimeError('extension overlaps classical parent')
 pkg=B/'package-lib';libs={x['name'] for x in tomllib.loads((tree/'lakefile.toml').read_text())['lean_lib']};leaked=[n for n in libs if n!='Foundation' and (pkg/n).exists()]
 if leaked:raise RuntimeError('project namespace leaked into package mirror: '+str(leaked))
 for n in list(g['order'])+jm['order']:
  p=C/'lib'/Path(n.replace('.','/')+'.olean');dest=lib/Path(n.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(p.resolve())
 for n in M['order']:
  p=(PACKET/M['extension_source_locations'][n]).resolve();need(p,M['source_sha256'][n],'extension frozen source');shutil.copyfile(p,src/Path(n.replace('.','/')+'.lean'))
 cs_hash=sha(CS);bs_hash=sha(bsfile);lean=Path(subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,text=True).strip()).resolve();need(lean,g['anchors']['lean_binary'],'Lean binary');env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 def audit():
  need(PACKET/'manifest.json',s['manifest_sha256'],'manifest');need(PACKET/'replay.py',executed,'driver');need(PACKET/'run.py',launcher,'launcher');need(CS,cs_hash,'classical join state');need(bsfile,bs_hash,'848 state')
  for key,p in refs.items():
   keysha=key+'_sha256' if key!='parent_snapshot' else 'parent_snapshot_sha256';need(p,M[keysha],key)
  need(tree/'lakefile.toml',g['anchors']['lakefile'],'frozen Lake config');need(lean,g['anchors']['lean_binary'],'Lean binary')
  if bs.get('rebase_from'):need(Path(bs['rebase_from'])/'state.json',bs['rebase_state_sha256'],'848 prior state')
  for n in g['order']:
   z=br[n];need(tree/g['sources'][n],g['source_hashes'][n],'parent frozen source');need(B/'source-snapshots'/(n.replace('.','_')+'.lean'),g['source_hashes'][n],'parent source snapshot');need(B/'lib'/Path(n.replace('.','/')+'.olean'),z['object_sha256'],'848 object');need(C/'lib'/Path(n.replace('.','/')+'.olean'),z['object_sha256'],'classical join parent object');need(lib/Path(n.replace('.','/')+'.olean'),z['object_sha256'],'extension parent object');need(B/'logs'/z['log_file'],z['log_sha256'],'848 log')
   if z.get('reused_from'):
    need(B/'transitive-manifests'/z['transitive_manifest'],z['transitive_manifest_sha256'],'reuse manifest');need(Path(z['original_compile_root'])/'state.json',z['original_compile_state_sha256'],'original compile state')
  for n in jm['order']:
   z=cr[n];need((refs['classical_join_manifest'].parent/jm.get('source_locations',{}).get(n,'frozen/'+n.rsplit('.',1)[1]+'.lean')).resolve(),jm['source_sha256'][n],'classical frozen suffix');need(C/'lib'/Path(n.replace('.','/')+'.olean'),z['object_sha256'],'classical suffix object');need(lib/Path(n.replace('.','/')+'.olean'),z['object_sha256'],'extension inherited suffix');need(C/'logs'/(n.replace('.','_')+'.log'),z['log_sha256'],'classical suffix log')
   for d,h in z['dependency_hashes'].items():need((C/'lib' if d in br or d in cr else pkg)/Path(d.replace('.','/')+'.olean'),h,'classical suffix dependency')
  for n,p in g['external_paths'].items():need(Path(p),g['external_hashes'][n],'direct external');need(pkg/Path(n.replace('.','/')+'.olean'),g['external_hashes'][n],'mirrored direct external')
  for rel,z in g['external_companions'].items():need(Path(z['path']),z['sha256'],'external companion');need(pkg/rel,z['sha256'],'mirrored companion')
  for fs in jm['extra_external_files'].values():
   for rel,h in fs.items():need(pkg/rel,h,'classical suffix external')
  for n,h in M['source_sha256'].items():need((PACKET/M['extension_source_locations'][n]).resolve(),h,'frozen extension source');need(src/Path(n.replace('.','/')+'.lean'),h,'working extension source')
 s.update(phase='parent authentication',classical_state_sha256=cs_hash,parent_state_sha256=bs_hash);save();audit();allowed=set(br)|set(cr)|set(M['order']);external=set(g['external_hashes'])|set(jm['extra_external'])
 for n in M['order']:
  s.update(phase='compile',module=n);save();f=src/Path(n.replace('.','/')+'.lean');o=lib/Path(n.replace('.','/')+'.olean');l=logs/(n.replace('.','_')+'.log');deps={}
  for line in f.read_text().splitlines():
   z=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
   if not z:continue
   for dep in z.group(1).split():
    if dep in allowed:q=lib/Path(dep.replace('.','/')+'.olean')
    elif dep in external:q=pkg/Path(dep.replace('.','/')+'.olean')
    else:raise RuntimeError('unaccounted declared import '+dep+' in '+n)
    if not q.is_file():raise RuntimeError('missing declared dependency '+dep+' in '+n)
    deps[dep]=sha(q)
  t=time.monotonic()
  with l.open('w') as out:p=subprocess.run([str(lean),'-M8000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
  text=l.read_text();row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'dependency_hashes':deps,'warning_lines':[x for x in text.splitlines() if re.search(r'(^|:)\s*warning:',x)]};s['records'].append(row);save()
  if p.returncode or re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b',text):raise RuntimeError('compile failed: '+n+'\n'+text)
  for dep,h in deps.items():need((lib if dep in allowed else pkg)/Path(dep.replace('.','/')+'.olean'),h,'dependency after compilation')
  if n.endswith('Checks'):
   groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
   if len(groups)!=1 or any({x.strip() for x in g0.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for g0 in groups):raise RuntimeError('unexpected endpoint axiom checks')
  print('PASS',n,round(row['seconds'],1),flush=True)
 s.update(phase='final authentication',module=None);save();audit()
 for row in s['records']:
  n=row['module'];need(lib/Path(n.replace('.','/')+'.olean'),row['object_sha256'],'extension output');need(logs/(n.replace('.','_')+'.log'),row['log_sha256'],'extension log')
  for dep,h in row['dependency_hashes'].items():need((lib if dep in allowed else pkg)/Path(dep.replace('.','/')+'.olean'),h,'extension final dependency')
 s.update(status='PASS',phase='complete');save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure={'type':type(e).__name__,'message':str(e),'phase':s.get('phase'),'module':s.get('module')});save();print('FAILED',s['failure'],flush=True);raise
