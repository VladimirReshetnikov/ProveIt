from pathlib import Path
import hashlib,json,re,collections
B=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
load=lambda p:json.loads(Path(p).read_text())
checks=[]
def ck(v,s):
 assert v,s
 checks.append(s)
P=B/'run2/verification.json';r=load(P)
ck(sha(P)=='cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701','actual identity')
ck(r['status']=='PASS' and not r['prepare_only'] and (r['named_axiom_probes'],r['callers'],r['warnings'])==(9,10,0),'actual census')
for run in ['run1','run2','prepared1','prepared2']:
 z=load(B/run/'verification.json');ck(z['before']==z['after'] and z['all_input_provider_postchecks'],'stable '+run)
 for p,h in z['before'].items():ck(sha(p)==h,'current '+p)
 for k in ['source','audit']:ck(sha(z[k]['path'])==sha(z[k]['snapshot'])==z[k]['sha256'],'snapshots '+run+k)
 for c in z['commands']:ck(Path(c['log']).read_text()==c['output'] and sha(c['log'])==c['log_sha256'],'raw log '+run)
 if run.startswith('prepared'):ck(z['status']=='PREPARED_NOT_BUILT' and z['commands']==z['fresh_modules']==[],'unbuilt '+run)
 if run=='run1':
  ck(z['status']=='FAIL' and len(z['commands'])==1 and z['fresh_modules']==[],'first fail no audit/object')
  out=z['commands'][0]['output'];ck(out.count('error:')==1 and 'ofProgram' in out and 'Tactic `rewrite` failed' in out and 'warning:' not in out,'exact rewrite failure')
ck(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],'default limits')
ck(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'no extra execution')
ck([c['label'] for c in r['commands']]==['source','audit'],'sequential proof pair')
for i,c in enumerate(r['commands']):
 ck(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'command success')
 ck(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'exact command')
 ck('warning:' not in c['output'] and 'sorryAx' not in c['output'],'no warning or untrusted output')
ck(sum(c['seconds']for c in r['commands'])<120,'shared duration')
f=r['fresh_modules'][0];ck(len(r['fresh_modules'])==1 and r['source_object_recorded_before_audit'] and r['all_fresh_objects_unchanged_after_audit'],'fresh scope')
ck(r['source_pass_object']==dict(f,source_command_index=0),'preaudit object')
ck(r['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'preaudit first')
ck(sha(f['path'])==f['sha256'] and f['source_sha256']==r['source']['sha256'],'current fresh')
roots=[Path(r['LEAN_PATH']),Path(r['compiler']['path']).parent.parent/'lib/lean']
def first(m):return next((p/Path(m.replace('.','/')).with_suffix('.olean')).resolve()for p in roots if(p/Path(m.replace('.','/')).with_suffix('.olean')).is_file())
for q in r['actual_first_providers']:ck(first(q['module'])==Path(q['actual_first']).resolve() and sha(first(q['module']))==q['sha256'],'actual first '+q['module'])
ck(first(f['module'])==Path(f['path']).resolve(),'fresh first actual')
projects={q['module']:q for q in r['reused_modules']};seen=set();external={'Init'}
def dfs(m):
 if m not in projects:external.add(m);return
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):dfs(n)
for m in re.findall(r'^import\s+(\S+)\s*$',Path(r['source']['path']).read_text(),re.M):dfs(m)
ck(seen==set(projects)==set(r['exact_project_import_closure']) and len(seen)==8,'eight-provider DFS')
ck(external=={q['module']for q in r['toolchain_providers']}=={'Init'},'Init only')
pool={}
for ep in r['provider_evidence']:
 ck(sha(ep['path'])==ep['sha256'],'parent pin');e=load(ep['path']);pf=e['fresh_modules'][0]
 for q in e['reused_modules']+[dict(module=pf['module'],source=e['source']['path'],source_sha256=pf['source_sha256'],object=pf['path'],object_sha256=pf['sha256'])]:
  q={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']};ck(q['module']not in pool or pool[q['module']]==q,'shared parent identity');pool[q['module']]=q
ck(pool==projects,'parent union exact')
for q in projects.values():
 for k in ['source','object']:ck(sha(q[k])==q[k+'_sha256'],'provider '+k)
audit=Path(r['audit']['path']).read_text();names=re.findall(r'^#print axioms (\S+)$',audit,re.M)
raw=re.findall(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",r['commands'][1]['output'],re.M)
parsed=[dict(name=n,axioms=sorted(x.strip()for x in ax.split(',')if x.strip()))for n,ax,_ in raw]
ck([q['name']for q in parsed]==names and len(names)==9 and parsed==r['axiom_reports'],'raw nine reports')
ck(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'}for q in parsed)and len(re.findall(r'^example\b',audit,re.M))==10,'standard axioms and typed10')
a=(B/'SourceRotation244.lean').read_text();s=Path(r['source']['path']).read_text()
ck(s==a.replace('      rw [hn]\n','      dsimp only [ofProgram]\n      rw [hn]\n'),'one unfold exact inverse')
g=(B/'check.py').read_text();g2=(B/'check-v2.py').read_text();oldb=load(B/'boundary.json');newb=load(B/'boundary-v2.json')
for old,new in [(sha(B/'SourceRotation244.lean'),r['source']['sha256']),(sha(B/'boundary.json'),sha(B/'boundary-v2.json')),("default=HERE/'SourceRotation244.lean'","default=HERE/'source-v2/SourceRotation244.lean'"),("default=HERE/'boundary.json'","default=HERE/'boundary-v2.json'")]:
 ck(g.count(old)==1,'one guard replacement');g=g.replace(old,new)
ck(g==g2,'guard only four binding/default literals')
for k in ['parents','compiler','reused_modules','toolchain_providers','scope']:ck(oldb[k]==newb[k],'boundary preserved '+k)
archive=B/'history/attempt1-before-roundtrip-unfold/archive.json';ar=load(archive)
for q in ar['files']:ck(sha(q['original']['path'])==q['original']['sha256']==sha(q['preserved']['path'])==q['preserved']['sha256'],'history roundtrip')
result=dict(status='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS',findings=[],verification=desc(P),source=desc(r['source']['path']),audit=desc(r['audit']['path']),guard=desc(B/'check-v2.py'),boundary=desc(B/'boundary-v2.json'),reviewer_source=desc(__file__),reviewer_role='Independent of concrete source/audit/guard/repair and root execution; author of its two imported checked generic loop/context lemmas. Prior source-only peer missed this elaboration unfolding issue and remains preserved.',counts=dict(inputs=len(r['before']),projects=8,probes=9,callers=10,warnings=0),fresh_object=f,scope=r['scope'],axiom_distribution={','.join(k)if k else'empty':v for k,v in collections.Counter(tuple(q['axioms'])for q in parsed).items()},failure=desc(B/'run1/verification.json'),repair=desc(B/'roundtrip-unfold-repair.json'),history=desc(archive),preparations=[desc(B/x/'verification.json')for x in ['prepared1','prepared2']],prior_source_review=desc(B/'independent-source-guard-review.json'),supplied_execution=False,check_count=len(checks),checks=checks)
(B/'independent-run2-evidence-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(review=desc(B/'independent-run2-evidence-review.json'),counts=result['counts'],checks=len(checks))))
