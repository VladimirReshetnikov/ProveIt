#!/usr/bin/env python3
"""Draft: source-directed 73-module join atop a completed isolated 14 provider."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile,time,tomllib
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
M=json.loads((PACKET/'manifest.json').read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
executed_driver_sha=os.environ.get('PRA14_JOIN_EXEC_SHA256');launcher_sha=os.environ.get('PRA14_JOIN_LAUNCHER_SHA256')
if not executed_driver_sha or not launcher_sha:raise SystemExit('use run.py so executed driver bytes are authenticated')
parser=argparse.ArgumentParser();parser.add_argument('--parent',type=Path,required=True);args=parser.parse_args();P=args.parent.resolve();PS=P/'state.json'
work=Path(tempfile.mkdtemp(prefix='pra14-zfc-join-'));src=work/'src';lib=work/'lib';logs=work/'logs';logs.mkdir();(src/'DiophantineConsistency').mkdir(parents=True);lib.mkdir()
state={'status':'RUNNING','phase':'initialization','root':str(work),'parent':str(P),'manifest_sha256':sha(PACKET/'manifest.json'),'driver_sha256':executed_driver_sha,'launcher_sha256':launcher_sha,'records':[],'scope':'Source-directed suffix on a single isolated 14-equation provider. Declared imports and selected direct package objects are guarded; dynamic imports and package-transitive ancestry remain inherited.'}
def save():
 q=work/'state.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(work/'state.json')
def need(p,h,reason):
 if not p.is_file() or sha(p)!=h:raise RuntimeError(reason+': '+str(p))
save();print('ROOT',work,flush=True)
try:
 need(PACKET/'replay.py',executed_driver_sha,'executed driver at startup');need(PACKET/'run.py',launcher_sha,'launcher at startup')
 baseline=(PACKET/M['parent_graph_audit']).resolve();need(baseline,M['parent_graph_audit_sha256'],'source audit');snapshot=(PACKET/M['parent_graph_snapshot_manifest']).resolve();need(snapshot,M['parent_graph_snapshot_manifest_sha256'],'snapshot manifest');expected=json.loads(baseline.read_text())['graph'];pm=json.loads(snapshot.read_text());tree=Path(pm['root'])/'tree';parent=json.loads(PS.read_text());assert parent['status']=='PASS','parent is not PASS';assert len(parent['records'])==len(expected['order'])==847
 parent_state_sha=sha(PS);g=parent['graph']
 for k in ('sources','edges','order','source_hashes','external_paths','external_hashes','external_companions','anchors'):
  if g[k]!=expected[k]:raise RuntimeError('parent graph differs: '+k)
 if any(not r.get('verified') for r in parent['records']):raise RuntimeError('parent has unverified records')
 if len(set(M['order']))!=len(M['order']) or set(M['order']) & set(g['sources']):raise RuntimeError('suffix order overlaps parent or has duplicates')
 prior=Path(parent['rebase_from'])/'state.json' if parent.get('rebase_from') else None
 if prior:need(prior,parent['rebase_state_sha256'],'parent prior state')
 records={r['module']:r for r in parent['records']};assert set(records)==set(g['order'])
 for n in M['order']:
  name=n.rsplit('.',1)[1];f=(PACKET/M['source_locations'][n]).resolve();need(f,M['source_sha256'][n],'packet source');shutil.copyfile(f,src/'DiophantineConsistency'/(name+'.lean'))
 for n in g['order']:
  source=P/'lib'/(n.replace('.','/')+'.olean');dst=lib/(n.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(source.resolve())
 pkg=P/'package-lib';libs={x['name'] for x in tomllib.loads((tree/'lakefile.toml').read_text())['lean_lib']};leaked=[n for n in libs if n!='Foundation' and (pkg/n).exists()]
 if leaked:raise RuntimeError('project namespace leaked into package mirror: '+str(leaked))
 lean=Path(subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,text=True).strip()).resolve();need(lean,g['anchors']['lean_binary'],'Lean binary');env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 def audit():
  need(PACKET/'manifest.json',state['manifest_sha256'],'manifest');need(PACKET/'replay.py',state['driver_sha256'],'executed driver');need(PACKET/'run.py',state['launcher_sha256'],'launcher');need(PS,parent_state_sha,'parent state');need(baseline,M['parent_graph_audit_sha256'],'parent source audit');need(snapshot,M['parent_graph_snapshot_manifest_sha256'],'snapshot manifest');need(lean,g['anchors']['lean_binary'],'Lean binary');need(tree/'lakefile.toml',g['anchors']['lakefile'],'frozen lakefile')
  if prior:need(prior,parent['rebase_state_sha256'],'parent prior state')
  for n in g['order']:
   rec=records[n];need(tree/g['sources'][n],g['source_hashes'][n],'parent frozen source');need(P/'source-snapshots'/(n.replace('.','_')+'.lean'),g['source_hashes'][n],'parent source snapshot');need(P/'lib'/(n.replace('.','/')+'.olean'),rec['object_sha256'],'parent output');need(lib/(n.replace('.','/')+'.olean'),rec['object_sha256'],'joined parent output');need(P/'logs'/rec['log_file'],rec['log_sha256'],'parent log')
   if rec.get('reused_from'):
    need(P/'transitive-manifests'/rec['transitive_manifest'],rec['transitive_manifest_sha256'],'parent reuse manifest');need(Path(rec['original_compile_root'])/'state.json',rec['original_compile_state_sha256'],'original compile state')
  for n,p in g['external_paths'].items():
   need(Path(p),g['external_hashes'][n],'parent direct external');need(pkg/(n.replace('.','/')+'.olean'),g['external_hashes'][n],'mirrored parent direct external')
  for rel,v in g['external_companions'].items():need(Path(v['path']),v['sha256'],'parent external companion');need(pkg/rel,v['sha256'],'parent mirrored companion')
  for files in M['extra_external_files'].values():
   for rel,h in files.items():need(pkg/rel,h,'suffix external object/companion')
  for p,h in M['strict_source_manifest_sha256'].items():need(Path(p),h,'strict source manifest')
  for n,h in M['source_sha256'].items():need((PACKET/M['source_locations'][n]).resolve(),h,'frozen suffix source');need(src/(n.replace('.','/')+'.lean'),h,'working suffix source')
 state['phase']='parent authentication';state['parent_state_sha256']=parent_state_sha;save();audit()
 allowed=set(g['sources'])|set(M['order']);external=set(g['external_hashes'])|set(M['extra_external'])
 for n in M['order']:
  state.update(phase='compile',module=n);save();f=src/(n.replace('.','/')+'.lean');obj=lib/(n.replace('.','/')+'.olean');log=logs/(n.replace('.','_')+'.log');deps={}
  for line in f.read_text().splitlines():
   m=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
   if not m:continue
   for dep in m.group(1).split():
    if dep in allowed:q=lib/(dep.replace('.','/')+'.olean')
    elif dep in external:q=pkg/(dep.replace('.','/')+'.olean')
    else:raise RuntimeError('unaccounted declared import '+dep+' in '+n)
    if not q.is_file():raise RuntimeError('missing declared import '+dep+' in '+n)
    deps[dep]=sha(q)
  t=time.monotonic()
  with log.open('w') as out:r=subprocess.run([str(lean),'-M8000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
  text=log.read_text();row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'dependency_hashes':deps,'warning_lines':[x for x in text.splitlines() if re.search(r'(^|:)\s*warning:',x)]};state['records'].append(row);save()
  if r.returncode or re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b',text):raise RuntimeError('compile failed: '+n+'\n'+text)
  for dep,h in deps.items():need((lib if dep in allowed else pkg)/(dep.replace('.','/')+'.olean'),h,'dependency after compilation')
  if n.endswith('Checks'):
   groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
   if len(groups)!=1 or any({x.strip() for x in x.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for x in groups):raise RuntimeError('unexpected endpoint axiom checks')
  print('PASS',n,round(row['seconds'],1),flush=True)
 state.update(phase='final authentication',module=None);save();audit()
 for row in state['records']:
  n=row['module'];need(lib/(n.replace('.','/')+'.olean'),row['object_sha256'],'suffix output');need(logs/(n.replace('.','_')+'.log'),row['log_sha256'],'suffix log')
  for dep,h in row['dependency_hashes'].items():need((lib if dep in allowed else pkg)/(dep.replace('.','/')+'.olean'),h,'final dependency')
 state.update(status='PASS',phase='complete',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure={'type':type(e).__name__,'message':str(e),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',state['failure'],flush=True);raise
