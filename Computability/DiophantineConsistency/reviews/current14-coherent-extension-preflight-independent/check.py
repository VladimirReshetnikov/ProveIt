#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];repo=D.parents[1];p=D/'research/current14-coherent-extension-preflight';sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest();assert sha(p/'inspect.py')=='23e1ba624220da6615bfe8046e4e82403dcd3617b5e92efc30816b70fb059a1d' and sha(p/'observation.json')=='f06cd481f1fbeb537cc2b7ce60e406e8e92f514cc5fbf678a805b82478fc4db3';obs=json.loads((p/'observation.json').read_bytes());assert obs['status']=='OBSERVATION_NOT_BUILD_READINESS' and obs['script_sha256']==sha(p/'inspect.py')
rerun=subprocess.run([sys.executable,'-I','-S','-B',str(p/'inspect.py')],cwd=repo,capture_output=True,text=True,check=True,timeout=180);assert not rerun.stderr;fresh=json.loads(rerun.stdout)
for k in ('fresh','host','quoted','union'):assert fresh[k]==obs[k]
assert fresh['pins']['git_head_before']==fresh['pins']['git_head_after']==obs['pins']['git_head_before']==obs['pins']['git_head_after']
assert fresh['fresh']['modules']==1000 and fresh['fresh']['observed_input_edges']==4179 and fresh['fresh']['input_companion_guards']==11050
for k in ('point_in_time_issues','workspace_source_drift','workspace_source_missing'):assert not fresh['fresh'][k]
h=fresh['host'];q=fresh['quoted'];u=fresh['union'];assert h['modules']==452 and h['fresh_overlap']==196 and h['fresh_extra']==256 and len(h['external_import_names'])==91 and len(h['external_names_new_to_fresh_manifest'])==25 and len(h['external_observed'])==91
for k in ('external_missing','untracked_source_modules','source_modules_differing_from_head','missing_project'):assert not h[k]
assert q['observed_project_objects']==259 and q['counts']=={'fresh_match_same_route':21,'partial_parent_FAILED':7,'pass_parent':231} and q['captured_direct_guard_checks']==33420 and len(q['traced'])==238
for k in ('captured_external_route_conflicts','issues','namespace_object_hash_conflicts','declared_direct_import_mismatches','traced_without_workspace_source_copy','traced_without_git_tracked_source_copy','traced_without_clean_head_source_copy','source_disagreements_with_host'):assert not q[k]
# Recheck each producer's success metadata, snapshot, object, both captured logs and guards.
partial=[];guard_count=0;log_count=0
for name,r in q['traced'].items():
 state=Path(r['producer_state']);assert sha(state)==r['producer_state_sha256'];d=json.loads(state.read_bytes());assert d['status']==r['parent_status'];rows=d.get('rows') or d.get('records') or [];matches=[x for x in rows if x.get('module','').split('.')[-1]==name.split('.')[-1] and x.get('object_sha256')==r['object_sha256']];assert len(matches)==1;stage=matches[0];assert sha(r['snapshot'])==r['source_sha256']==stage['source_sha256'] and sha(r['object'])==r['object_sha256']
 for ph in ('deps','compile'):
  x=stage.get(ph) or stage.get(ph+'_run');assert x and x['exit']==0 and x.get('stop_reason') is None and not x.get('monitor_errors') and not x.get('observed_descendant_pids');path=Path(x.get('log') or (state.parent/(name.split('.')[-1]+'-'+ph+'.txt')));assert sha(path)==x['log_sha256'];log_count+=1
 guards=stage.get('direct_guard') or stage.get('guard');assert isinstance(guards,dict)
 for path,val in guards.items():
  z=Path(path);guard_count+=1
  if val is None:assert not os.path.lexists(z)
  else:assert z.is_file() and str(z.resolve())==val['realpath'] and sha(z)==val['sha256']
 if d['status']!='PASS':partial.append(name);assert d['status']=='FAILED'
assert len(partial)==7 and guard_count==33420 and log_count==476
# Independently verify union order against every recorded host/import and quote/direct edge.
base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_bytes());base_names={r['module'] for r in base['records']};host_extra=set(h['sources'])-base_names;quoted=set(q['traced']);assert len(host_extra)==256 and len(quoted)==238 and len(host_extra&quoted)==4;union=host_extra|quoted;order=u['observed_union_topological_order'];assert len(union)==len(order)==len(set(order))==490 and set(order)==union
position={x:i for i,x in enumerate(order)}
for n in union:
 deps=set(h['sources'].get(n,{}).get('imports',[]))|set(q['traced'].get(n,{}).get('dependencies',{}))
 assert all(position[d]<position[n] for d in deps if d in union)
# Match each host source and at least one clean quoted source to an actual HEAD blob,
# rather than relying only on git diff name output.
head=fresh['pins']['git_head_before'];tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=repo).decode().split('\0'));dirty=set(subprocess.check_output(['git','diff','--name-only','-z',head,'--'],cwd=repo).decode().split('\0'));paths={}
for r in h['sources'].values():
 path=r['path'];assert path in tracked and path not in dirty;paths.setdefault(path,r['sha256']);assert paths[path]==r['sha256']
for r in q['traced'].values():
 choices=[x for x in r['workspace_source_copies'] if x in tracked and x not in dirty];assert choices;path=choices[0];paths.setdefault(path,r['source_sha256']);assert paths[path]==r['source_sha256']
requests=[head+':'+x for x in paths];proc=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(requests)+'\n').encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=repo,check=True,timeout=180);assert not proc.stderr;buf=proc.stdout;at=0
for path in paths:
 end=buf.index(b'\n',at);header=buf[at:end].split();assert len(header)==3 and header[1]==b'blob';size=int(header[2]);start=end+1;blob=buf[start:start+size];assert hashlib.sha256(blob).hexdigest()==paths[path] and buf[start+size:start+size+1]==b'\n';at=start+size+1
assert at==len(buf)
r=fresh['resources'];assert r['existing_guard_min_disk_bytes']==5000000000 and r['existing_guard_min_available_memory_bytes']==10*1024**3
print(json.dumps({'status':'PASS_INDEPENDENT_OBSERVATION_AUDIT','observed_union':490,'partial_failed_parent_stages':sorted(partial),'quoted_logs_verified':log_count,'quoted_guards':guard_count,'head_blob_paths':len(paths),'current_tmp_free_bytes':r['tmp_free_bytes'],'scope':'read-only captured-direct-edge and line-parsed source survey, not build readiness or full dependency ancestry'},indent=2))
