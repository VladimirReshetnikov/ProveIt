from pathlib import Path
import hashlib,json,re

B=Path('/tmp/zfc-rotation240-bootstrap')
O=Path('/tmp/zfc-rotation240-bootstrap-publication-design')
PINS=[
('bootstrap-first','d6c71cbd0d6a3ef9290f376107246141a0dd02aab2e9f91a52bd2923d1ec8277'),
('chunk001','1d8065f7715e8bb4e2d42bfd277a45ce64520cbf5b8fd4e6fbfafe5273c93f59'),
('chunk002','2e2445c90f3d01c78eaeeb7f190a52385fc3060bb32189708aa93f70f20b87d9'),
('chunk003','2f0446801d8277bb6a823f8a9ad40b7c682ccef7fa44ccb052e16de28fa3e470'),
('chunk004','880424a1caba0e92c6cc64b6d0f9ec0d6707762b02e7dbe84178011bbec890fb'),
('chunk005','90259501105ef39b1e558746a58865b56e5854e7dd0102e959450e50d84aeb97'),
('chunk006','0653d1e87d02274b0fd99eb51c877d98fdfb892f3d38e321352ff447074a91d9'),
('chunk007','c1314ee7343111dae707c441b441a18ce5f6d19aa84befa2c8af144a19207353'),
('chunk008','19a219ed4e6013dfc113124cb1945154f70dcb2b65bb2fe21b164fd2eb0f00a1'),
('chunk009','68a2b1c456d52039496842f2ed89051eaffee93059edd7e77ceccbeff293d239')]
checks=0;seen={}
def need(v,m):
 global checks
 checks+=1
 if not v:raise AssertionError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def verify(p,h=None):
 p=str(Path(p).absolute());h=h or sha(p)
 need(p not in seen or seen[p]==h,'Conflicting path pin '+p)
 if p not in seen:need(sha(p)==h,'Current bytes '+p);seen[p]=h
 return dict(path=p,sha256=h)
def load(p):verify(p);return json.loads(Path(p).read_text())
def imports(p):return re.findall(r'^import (\S+)\s*$',Path(p).read_text(),re.M)
def first_object(record,module):
 rel=Path(*module.split('.')).with_suffix('.olean')
 roots=[Path(p) for p in record['LEAN_PATH'].split(':')]+[Path(record['compiler']['path']).parent.parent/'lib/lean']
 candidates=[r/rel for r in roots if (r/rel).is_file()]
 need(bool(candidates),'Provider resolution '+module);return str(candidates[0].resolve())
units=[];endpoint=0;prior=None;prior_inv=None;prior_data=None;all_segments=[]
for index,(slug,pin) in enumerate(PINS):
 base=B/slug;rp=base/'run1/verification.json';verify(rp,pin);r=load(rp)
 ip=base/'source-inventory.json';inv=load(ip);dp=Path(inv['data']['path']);data=load(dp)
 need(r['status']=='PASS' and r['prepare_only'] is False,'Actual terminal PASS')
 need(r['warnings']==0 and r['only_standard_axioms'],'Clean axiom boundary')
 need(r['before']==r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'],'Recorded postchecks')
 need((r['shared_timeout_seconds'],r['memory_mebibytes'],r['LEAN_NUM_THREADS'])==(120,4096,'1'),'Unchanged resource policy')
 need(r['global_option_overrides']==[] and not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'No override/build/download/version')
 for p,h in r['before'].items():verify(p,h)
 for role in ('source','audit'):
  d=r[role];verify(d['path'],d['sha256']);verify(d['snapshot'],d['sha256']);need({k:d[k] for k in ('path','sha256')}==inv[role],'Exact generated '+role)
 for role in ('data','generator','canonical'):verify(inv[role]['path'],inv[role]['sha256'])
 verify(r['boundary']['path'],r['boundary']['sha256']);guard=verify(base/'check.py')
 need(r['before'][guard['path']]==guard['sha256'],'Executed guard identity')
 p=load(base/'prepared1/verification.json')
 need(p['status']=='PREPARED_NOT_BUILT' and p['prepare_only'] and p['commands']==[] and p['fresh_modules']==[],'Actual preparation only')
 need(p['before']==p['after'] and p['all_input_provider_postchecks'],'Preparation postchecks')
 for f,h in p['before'].items():verify(f,h)
 need(p['reused_modules']==r['reused_modules'] and p['toolchain_providers']==r['toolchain_providers'],'Preparation/actual same provider identities')
 for role in ('source','audit'):
  need(p[role]['sha256']==r[role]['sha256'],'Preparation same '+role);verify(p[role]['snapshot'],p[role]['sha256'])
 need([c['label'] for c in r['commands']]==['source','audit'],'Source then audit')
 for c in r['commands']:
  need(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'Terminal command')
  need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'],'Exact compiler arguments')
  verify(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Exact raw output')
  need('warning:' not in c['output'] and 'sorryAx' not in c['output'],'No warnings/sorry')
 need(sum(c['seconds'] for c in r['commands'])<120,'Shared actual duration')
 audit=Path(r['audit']['path']).read_text();source=Path(r['source']['path']).read_text()
 names=re.findall(r'^#print axioms (\S+)\s*$',audit,re.M)
 reports=[dict(name=n,axioms=sorted({a.strip() for a in ax.split(',') if a.strip()})) for n,ax in re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)]
 need(names==inv['probes']==[x['name'] for x in reports] and reports==r['axiom_reports'],'Exact ordered raw probes')
 need(len(names)==r['named_axiom_probes'] and len(re.findall(r'^example\b',audit,re.M))==inv['callers']==r['callers'],'Exact typed census')
 need(all(set(x['axioms'])<={'propext','Quot.sound','Classical.choice'} for x in reports),'Standard axiom sets')
 need(len(r['fresh_modules'])==1 and r['source_object_recorded_before_audit'],'Fresh object capture')
 fresh=r['fresh_modules'][0];verify(fresh['path'],fresh['sha256'])
 need(fresh['module']==inv['module'] and fresh['source_sha256']==r['source']['sha256'],'Fresh module/source')
 need(r['source_pass_object']==dict(fresh,source_command_index=0),'Source-pass capture')
 need(r['fresh_first_provider_before_audit']=={k:fresh[k] for k in ('module','path','sha256')},'Pre-audit first-provider capture')
 need(first_object(r,fresh['module'])==str(Path(fresh['path']).resolve()),'Fresh actual first')
 providers={x['module']:x for x in r['reused_modules']};tools={x['module']:x for x in r['toolchain_providers']}
 need(len(providers)==4+index==r['exact_project_prerequisite_count'] and set(tools)=={'Init','Lean.Elab.Tactic.Omega'},'Growing exact project/tool boundary')
 actual={x['module']:x for x in r['actual_first_providers']};need(set(actual)==set(providers)|set(tools),'Exact first-provider census')
 reached=set();visiting=set()
 def dfs(m):
  if m in tools:return
  need(m in providers and m not in visiting,'Known acyclic import '+m)
  if m in reached:return
  visiting.add(m)
  for child in imports(providers[m]['source']):dfs(child)
  visiting.remove(m);reached.add(m)
 for m in imports(r['source']['path']):dfs(m)
 need(reached==set(providers)==set(r['exact_project_import_closure']),'Exact source import DFS')
 for m,x in providers.items():
  verify(x['source'],x['source_sha256']);verify(x['object'],x['object_sha256'])
  expected=str(Path(x['object']).resolve());need(first_object(r,m)==expected==actual[m]['actual_first'],'Project actual first '+m)
  need(actual[m]['sha256']==x['object_sha256'],'First hash '+m)
 for m,x in tools.items():
  verify(x['object'],x['object_sha256']);need(first_object(r,m)==str(Path(x['object']).resolve())==actual[m]['actual_first'],'Tool actual first '+m)
 need(inv['unit_index']==index and inv['start']==endpoint and inv['segments']==data['segments'],'Consecutive unit start')
 need(imports(r['source']['path'])==inv['imports'],'Inventory actual imports')
 need('set_option' not in source and 'native_decide' not in source and 'sorry' not in source,'Default kernel proof source')
 need(len(inv['parents'])==1,'One predecessor')
 parent=inv['parents'][0];verify(parent['path'],parent['sha256'])
 need(any(x['path']==parent['path'] and x['sha256']==parent['sha256'] for x in r['provider_evidence']),'Actual predecessor evidence')
 if index:
  need(parent['path']==prior['verification']['path'] and parent['sha256']==prior['verification']['sha256'],'Exact previous successful unit')
  need(inv['imports']==[prior_inv['module']],'Direct predecessor import')
  need(data['checkpoints'][str(endpoint)]==prior_data['checkpoints'][str(endpoint)],'Exact checkpoint boundary data')
 else:need(parent['sha256']=='f54e57fe7e2e4e7c26c57ef612a0f9958a167370c5f45a0c67f9d09d50f57df0','Actual Fast parent')
 for s in inv['segments']:
  need(s['start']==endpoint and s['end']==endpoint+2**s['depth'] and 0<=s['depth']<=14,'Exact contiguous block arithmetic')
  endpoint=s['end'];all_segments.append(s)
  cp=data['checkpoints'][str(endpoint)]
  pat=rf'def checkpoint{endpoint} : ZipConfig 240 :=\s*\{{ state := some ⟨(\d+), by decide⟩, head := (-?\d+),\s*left := (.*?),\s*right := (.*?) \}}'
  m=re.search(pat,source,re.S);need(m is not None,'Literal checkpoint '+str(endpoint))
  def bits(t):
   need(re.fullmatch(r'[\s\[\],+truefals]+',t) is not None,'Boolean-list-only syntax')
   return [int(x=='true') for x in re.findall(r'\b(true|false)\b',t)]
  need(int(m[1])==cp['state'] and int(m[2])==cp['head'] and bits(m[3])==cp['left'] and bits(m[4])==cp['right'],'Literal/data whole checkpoint')
  support=sorted([cp['head']-i-1 for i,x in enumerate(cp['left']) if x]+[cp['head']+i for i,x in enumerate(cp['right']) if x])
  need(support==cp['ones'],'Complete finite support, not simulation')
  need(f'theorem block{endpoint} : zipBlock fastMachine {s["depth"]} ' in source and f'= checkpoint{endpoint} := by\n  decide +kernel' in source,'Kernel block obligation')
 need(inv['endpoint']==endpoint and inv['final_target']==409691,'Endpoint inventory')
 unit=dict(unit=slug,index=index,module=inv['module'],verification=verify(rp,pin),source=inv['source'],audit=inv['audit'],guard=guard,boundary=r['boundary'],preparation=verify(base/'prepared1/verification.json'),inventory=verify(ip),data=inv['data'],start=inv['start'],endpoint=endpoint,segments=inv['segments'],probes=r['named_axiom_probes'],callers=r['callers'],inputs=len(r['before']),providers=len(providers),fresh_module=fresh,source_seconds=r['commands'][0]['seconds'],audit_seconds=r['commands'][1]['seconds'])
 units.append(unit);prior=unit;prior_inv=inv;prior_data=data
need(endpoint==409691 and len(all_segments)==34,'Complete exact prefix')
need(sum(x['probes'] for x in units)==72 and sum(x['callers'] for x in units)==102,'Complete audit census')
final=prior_data['checkpoints']['409691'];need((final['state'],final['head'])==(84,-5) and final['left']==[1]+[0]*9 and len(final['right'])==707 and len(final['ones'])==351,'Exact final finite zipper')
need('theorem bootstrap409691 : ZipRep (machineRotation240.run 409691) checkpoint409691 := reached409691' in source and '∀ elapsed, elapsed ≤ 409691 → (machineRotation240.run elapsed).state ≠ none' in source,'Final closed API and activity')
batch=load(B/'batch2-9-run1/batch.json');need(batch['status']=='PASS_EXACT_409691_PREFIX' and batch['target']==409691,'Root terminal coordinator')
need(len(batch['commands'])==32 and [x['phase'] for x in batch['commands']]==['generate','bind','prepare','actual']*8,'Serial command phases')
for c in batch['commands']:need(c['exit_code']==0,'Coordinator command exit');verify(c['log'],c['log_sha256'])
verify('/tmp/zfc-rotation240-bootstrap-batch-root.py');verify(__file__)
for p,h in seen.items():need(sha(p)==h,'Close current rehash '+p)
receipt=dict(status='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS',findings=[],reviewer_role='Independent of current bootstrap generator, guards, source ports and root proof execution; author of related historical245 guard/source tooling and this publication plan.',reviewer_source=verify(__file__),units=units,probes=72,callers=102,warnings=0,steps=409691,blocks=34,source_seconds=sum(x['source_seconds'] for x in units),audit_seconds=sum(x['audit_seconds'] for x in units),final_literal=dict(state=84,head=-5,left=final['left'],right_word_length=707,one_count=351),checks=checks,current_unique_inputs=len(seen),current_inputs=seen,scope='Existing actual root proof evidence and static literal/chain review. No supplied script, generator, guard, simulator or compiler executed. Historical generic provider attestation limits remain those in actual records. Initial runtime Related/frame, decoder coverage and binary/PA calibration remain separate.',batch=verify(B/'batch2-9-run1/batch.json'))
out=O/'actual-review.json';need(not out.exists(),'Fresh immutable receipt');out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(path=str(out),sha256=sha(out),checks=checks,units=10,probes=72,callers=102)))
