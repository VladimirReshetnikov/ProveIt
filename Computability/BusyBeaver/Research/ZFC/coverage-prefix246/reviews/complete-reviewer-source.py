#!/usr/bin/env python3
"""Reviewer-owned read-only inspection of existing exact246 coverage evidence.
No supplied Python is imported or executed; no compiler, guard or version query.
Outputs only a new immutable review directory outside the repository/history.
"""
from pathlib import Path
import argparse,ast,collections,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage')
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PLAN='9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09'
GEN='174870fefd527465036748bd5649f9acde8dcfad3a46e8ee33884c888507e223'
TREE='7f4a3782f4ce061478a233d15272c15f2b2aedab688f728f7e7511f186216e71'
RECOVERY='489a13fa02e83342c824fa9dee64f133b8d65e188d2edadd8d25577e13588a5d'
NS='SetTheory.BusyBeaver.ZFC.SitesPrefix246.'
def digest(data):return hashlib.sha256(data).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def norm(s):return ' '.join(s.split())
def imports(s):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',s,re.M)
def bits(p):return '['+', '.join('true'if v else'false'for v in p)+']'
def goal(p):return 'allSites SitePrefix246.checkSite '+bits(p[::-1])+' (descend ActualTree254.tree '+bits(p)+') = true'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--pipeline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--require-complete',action='store_true');a=ap.parse_args()
 O=a.output.resolve();need(not O.exists()and not O.is_relative_to(R)and not O.is_relative_to(B),'New external review output required')
 checks=0;bindings={};physical={};path_targets={};read_texts={}
 def bind(path,h):
  nonlocal checks
  p=Path(path).absolute();key=str(p);real=str(p.resolve());checks+=1
  if key in bindings:need(bindings[key]==h,'Conflicting input pin '+key)
  else:bindings[key]=h
  if key in path_targets:need(path_targets[key]==real,'Input resolution changed '+key)
  else:path_targets[key]=real
  if real in physical:need(physical[real]==h,'Conflicting physical pin '+real)
  else:need(digest(p.read_bytes())==h,'Changed bytes '+key);physical[real]=h
  return p
 def text(path):
  p=str(Path(path).resolve())
  if p not in read_texts:read_texts[p]=Path(path).read_text()
  return read_texts[p]
 def load(path,h=None):
  raw=Path(path).read_bytes()
  if h is not None:bind(path,h)
  return json.loads(raw)
 mf=B/'guards-four/pipeline-manifest.json';gf=B/'plan-four/generation.json';plan=load(mf,PLAN);gen=load(gf,GEN)
 units=plan['units'];by={u['module']:u for u in units};need(len(units)==len(by)==102 and plan['full_plan'],'Exact full102 plan')
 need(sum(u['probes']for u in units)==sum(u['callers']for u in units)==468,'468 audit census')
 raw=a.pipeline.read_bytes();state=json.loads(raw);snapshot_hash=digest(raw)
 if a.require_complete:
  need(state['status']=='PASS_COMPLETE_PLAN'and state['full_plan']and state['endpoint_established']and state['pending']==[],'Final runner gate not reached')
  refs=state['available_records'];need(set(refs)==set(by),'Final102 selected record identities')
 else:
  refs=dict(state.get('reused',{}));refs.update(state.get('completed',{}))
  if state['status']=='PASS_COMPLETE_PLAN':need(False,'Use explicit final authorization mode after root confirmation')
 need(set(refs)<=set(by),'Unknown selected module')
 # Independently parse the literal actual decoder, then verify every recorded frontier path.
 treepath=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean';bind(treepath,TREE)
 body=text(treepath).split('def tree : Tree :=',1)[1].split('theorem tree_eq',1)[0]
 tokens=re.findall(r'\.[A-Za-z]+|[()]|\d+',body);need(re.sub(r'\.[A-Za-z]+|[()]|\d+|\s+','',body)=='','Unexpected decoder literal token');at=0
 def take():
  nonlocal at
  t=tokens[at];at+=1;return t
 def parse_edge():
  t=take()
  if t=='(':
   e=parse_edge();need(take()==')','Edge paren');return e
  need(t in ['.inc','.decnz','.brk','.cont','.halt'],'Edge constructor');return(t,0 if t=='.halt'else int(take()))
 def parse_tree():
  t=take()
  if t=='(':
   v=parse_tree();need(take()==')','Tree paren');return v
  if t=='.node':return('node',parse_tree(),parse_tree())
  need(t=='.leaf','Tree constructor');return('leaf',parse_edge())
 tree=parse_tree();need(at==len(tokens),'Complete decoder parse')
 def counts(t):
  if t[0]=='leaf':return(0,1,2 if t[1][0]=='.decnz'else 1,0)
  a,b=counts(t[1]),counts(t[2]);return(1+a[0]+b[0],a[1]+b[1],a[2]+b[2],1+max(a[3],b[3]))
 need(counts(tree)==(6459,6460,8391,34),'Actual decoder counts')
 def descend(p):
  t=tree
  for x in p:need(t[0]=='node','Path past leaf');t=t[2 if x else 1]
  return t
 cuts=gen['cut_frontier'];joins=gen['join_plan'];need(len(cuts)==233 and len(joins)==232,'Cut/join census')
 node_at={};cut_indices=[]
 for c in cuts:
  p=c['path'];need(counts(descend(p))==(c['nodes'],c['leaves'],c['guards'],c['depth']),'Cut actual subtree '+str(c['index']))
  need(c['guards']<=64,'Cut limit');node_at[tuple(p)]=('cut',c['index']);cut_indices.append(c['index'])
 need(cut_indices==list(range(233)),'Cut index enumeration')
 def endpoint(ref):return(cuts if ref[0]=='cut'else joins)[ref[1]]
 for j in joins:
  p=tuple(j['path']);need(descend(list(p))[0]=='node','Join actual node')
  for direction,k in [(False,'left'),(True,'right')]:
   q=endpoint(j[k]);need(tuple(q['path'])==p+(direction,)and node_at.get(tuple(q['path']))==tuple(j[k]),'Both-child structural join '+str(j['index']))
  node_at[p]=('join',j['index'])
 need(node_at.get(())==('join',231),'Closed root join')
 need(sum(c['leaves']for c in cuts)==6460 and sum(c['guards']for c in cuts)==8391,'All frontier cases accounted')
 for u in units:
  for pk,hk in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:bind(u[pk],u[hk])
  s=text(u['source_path']);au=text(u['audit_path']);g=text(u['guard']);ast.parse(g)
  need(imports(s)==u['imports'],'Literal source imports')
  need(not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s),'Unexpected source escape hatch')
  need(not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s),'Unexpected proof limits')
  names=re.findall(r'^#print axioms\s+(\S+)',au,re.M);need(names==[NS+n for n in u['probe_names']],'Typed audit probes')
  need(len(re.findall(r'^example\b',au,re.M))==u['callers'],'Typed caller census')
  if u['kind']=='closed_cuts':
   for i in u['cuts']:
    c=cuts[i];decl='theorem '+c['theorem']+' : '+goal(c['path'])+' := by decide +kernel'
    need(norm(decl)in norm(s),'Literal closed cut '+str(i));need(norm('example : '+goal(c['path'])+' := '+c['theorem'])in norm(au),'Cut typed caller')
  elif u['kind']=='binary_composition':
   for name in u['probe_names']:
    j=joins[int(name.split('_')[1])];p=j['path'];decl='theorem '+name+' : '+goal(p)+' := allSites_join SitePrefix246.checkSite '+bits(p[::-1])+' (descend ActualTree254.tree '+bits(p+[False])+') (descend ActualTree254.tree '+bits(p+[True])+') '+endpoint(j['left'])['theorem']+' '+endpoint(j['right'])['theorem']
    need(norm(decl)in norm(s),'Literal both-child join '+name);need(norm('example : '+goal(p)+' := '+name)in norm(au),'Join typed caller')
  else:need(u['module']=='BusyBeaver.ZFC.SitesPrefix246'and 'join_231'in s and 'ActualTree254.tree_eq all_sites P'in s,'Exact final endpoint source')
 # Cross-record file hashes are deduplicated; each metadata binding is still inspected.
 records={};record_hashes={};actual_guards={};totals=collections.Counter();warnings={};source_seconds=[];audit_seconds=[];module_identities={}
 for u in units:
  m=u['module']
  if m not in refs:continue
  ref=refs[m];p=Path(ref['path']).resolve();need(p.is_relative_to(B),'Record outside history');d=load(p,ref['sha256']);record_hashes[m]=ref['sha256']
  need(d['status']=='PASS'and not d['prepare_only']and d['only_standard_axioms'],'Actual PASS')
  need(d['before']==d['after']and d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit'],'Current input/fresh postchecks')
  need(d['source_object_recorded_before_audit']and len(d['fresh_modules'])==1,'Fresh-before-audit record')
  f=d['fresh_modules'][0];need(f['module']==m and f['source_sha256']==u['source_sha256']and f==d['source_pass_object']and f==ref['fresh'],'Fresh identity')
  bind(f['path'],f['sha256']);fb=d['fresh_first_provider_before_audit'];need((fb['module'],fb['sha256'],Path(fb['path']).resolve())==(m,f['sha256'],Path(f['path']).resolve()),'Fresh actual-first pre-audit')
  for kind in ['source','audit']:
   q=d[kind];need(q['sha256']==u[kind+'_sha256'],'Selected source/audit pin');bind(q['path'],q['sha256']);bind(q['snapshot'],q['sha256'])
  for q,h in d['before'].items():bind(q,h)
  c=d['compiler'];bind(c['path'],c['sha256']);need(c==state['compiler']and not c['compiler_version_query_performed'],'Fixed compiler identity/no query')
  need(not d['dependency_build']and not d['downloads']and d['external_project_boundaries']==[],'No hidden build/download/external project boundary')
  need(d['per_command_timeout_seconds']==d['shared_wall_seconds']==120,'Unit wall bound')
  cmds=d['commands'];need([x['label']for x in cmds]==['source','audit']and all(x['exit_code']==0 and not x.get('timed_out',False)for x in cmds),'Actual successful command order')
  for x in cmds:
   need(x['command'][0]==c['path']and '-j1'in x['command']and '-M4096'in x['command'],'Actual command resource flags')
   need(Path(x['command'][-1]).resolve()==Path(d[x['label']]['snapshot']).resolve(),'Actual input snapshot command')
   need((p.parent/(x['label']+'.log')).read_text()==x['output'],'Raw source/audit logs')
  need('-o'in cmds[0]['command']and cmds[0]['command'][cmds[0]['command'].index('-o')+1]==f['path'],'Actual fresh output command')
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",cmds[1]['output'],re.S)
  need([name for name,_ in reports]==[NS+n for n in u['probe_names']],'Exact ordered axiom reports')
  for name,ax in reports:
   vals=tuple(sorted(v.strip()for v in ax.split(',')if v.strip()));need(set(vals)<={'propext','Classical.choice','Quot.sound'},'Nonstandard axiom '+name);totals[str(vals)]+=1
  need((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Actual audit census')
  for label in ['source','audit']:need(d['warnings'][label]==cmds[0 if label=='source'else 1]['output'].count('warning:'),'Observed warning count')
  warnings[m]=d['warnings'];source_seconds.append(cmds[0]['seconds']);audit_seconds.append(cmds[1]['seconds'])
  for q in d['provider_evidence']:bind(q['path'],q['sha256'])
  providers={q['module']:q for q in d['reused_modules']};need(len(providers)==len(d['reused_modules'])==d['project_module_count']==u['expected_provider_count'],'Exact provider census')
  need(d['exact_project_import_closure'] is True,'Recorded provider closure')
  visited=[];active=set();toolnames={'Init'}
  def visit(n):
   if n=='Init'or n.startswith(('Lean.','Std.')):toolnames.add(n);return
   if n in visited:return
   need(n in providers and n not in active,'Missing/cyclic actual provider '+n);active.add(n);q=providers[n]
   bind(q['source'],q['source_sha256']);bind(q['object'],q['object_sha256'])
   identity=(q['source_sha256'],q['object_sha256'])
   if n in module_identities:need(module_identities[n]==identity,'Module changes across records '+n)
   else:module_identities[n]=identity
   for child in imports(text(q['source'])):visit(child)
   active.remove(n);visited.append(n)
  for n in imports(text(d['source']['path'])):visit(n)
  need(set(visited)==set(providers),'Actual import DFS closure')
  need(toolnames==set(d['actual_direct_tool_imports']),'Actual direct tool imports')
  roots=[Path(x)for x in d['LEAN_PATH'].split(':')if x];toolroot=Path(c['path']).parent.parent/'lib/lean'
  def first(n):
   rel=Path(*n.split('.')).with_suffix('.olean')
   for root in roots+[toolroot]:
    q=root/rel
    if q.exists():return q
   raise ValueError('No actual first provider '+n)
  firsts={q['module']:q for q in d['actual_first_providers']};need(set(firsts)==set(providers),'All project actual-first bindings')
  for n,q in firsts.items():
   need(first(n)==Path(q['actual_first'])and first(n).resolve()==Path(q['resolved']).resolve()==Path(providers[n]['object']).resolve(),'Actual search path first provider '+n)
   need(q['sha256']==providers[n]['object_sha256'],'First object SHA');bind(q['actual_first'],q['sha256'])
  need(first(m).resolve()==Path(f['path']).resolve(),'Fresh first provider on actual search path')
  tools={q['module']:q for q in d['toolchain_providers']};need(set(tools)==toolnames,'Explicit toolchain boundaries')
  for n,q in tools.items():bind(q['object'],q['object_sha256']);need(first(n).resolve()==Path(q['object']).resolve()and Path(q['actual_first']).resolve()==first(n).resolve(),'Tool first provider')
  gs=[(q,h)for q,h in d['before'].items()if q.endswith('.py')];need(len(gs)==1,'One actual guard');actual_guards[m]={'path':gs[0][0],'sha256':gs[0][1],'planned_sha256':u['guard_sha256'],'same_as_plan':gs[0][1]==u['guard_sha256']}
  records[m]={'path':str(p),'sha256':ref['sha256'],'fresh':f,'project_module_count':d['project_module_count'],'probes':d['named_axiom_probes'],'callers':d['callers'],'source_seconds':cmds[0]['seconds'],'audit_seconds':cmds[1]['seconds'],'warnings':d['warnings']}
 expected_reps={f'BusyBeaver.ZFC.SitesPrefix246Chunk{x:03d}'for x in [0,42,210]}
 need({m for m,g in actual_guards.items()if not g['same_as_plan']}==expected_reps&set(refs),'Only the3 representative guards differ')
 for m,row in records.items():
  f=row['fresh']
  if m in module_identities:need(module_identities[m]==(f['source_sha256'],f['sha256']),'Generated ancestor matches selected actual object')
 # Preserve and classify observed pipeline/proof history, without repairing any raw record.
 recovery=load(B/'recovery-after-session79413/recovery-review.json',RECOVERY);history=[];attempts=[]
 for p in sorted(B.rglob('pipeline.json')):
  if 'publication-design'in p.relative_to(B).parts:continue
  data=p.read_bytes();d=json.loads(data);ph=digest(data);active_current=p.resolve()==a.pipeline.resolve()and not a.require_complete
  stale=d['status']=='RUNNING'and not active_current
  if stale:need(str(p.resolve())==str(Path(recovery['pipeline']['path']).resolve())and ph==recovery['pipeline']['sha256'],'Unclassified stale runner')
  for x in d['attempts']:
   vp=Path(x['output'])/'verification.json';need(vp.exists(),'Unclassified no-record attempt')
   vd=load(vp);live=active_current and vd['status']=='RUNNING'
   if not live:
    need(vd['status']not in ['RUNNING','PREPARING'],'Unresolved historical proof record')
    if 'record'in x:bind(x['record']['path'],x['record']['sha256'])
    if 'log'in x:bind(x['log'],x['log_sha256'])
   attempts.append({'pipeline':str(p),'module':x['module'],'raw_attempt_status':x['status'],'verification_status':vd['status'],'record':str(vp),'live_at_snapshot':live})
  history.append({'path':str(p),'sha256':ph,'raw_status':d['status'],'stale_classified79413':stale,'active_current_snapshot':active_current,'attempts':len(d['attempts'])})
 if a.require_complete:
  need(len(records)==102 and sum(v['probes']for v in records.values())==sum(v['callers']for v in records.values())==468,'Complete selected census')
  final=records['BusyBeaver.ZFC.SitesPrefix246'];need(final['project_module_count']==125,'Final125 reused providers')
  fd=load(final['path']);generated={q['module']for q in fd['reused_modules']if q['module']in by};need(generated==set(by)-{'BusyBeaver.ZFC.SitesPrefix246'},'All101 generated ancestors')
  for path,target in path_targets.items():need(str(Path(path).resolve())==target,'End-of-review input resolution changed '+path)
  for path,h in physical.items():need(digest(Path(path).read_bytes())==h,'End-of-review current input changed '+path)
 O.mkdir();(O/'pipeline-snapshot.json').write_bytes(raw)
 result={'status':'PASS_COMPLETE_COVERAGE_EXISTING_EVIDENCE_REVIEW'if a.require_complete else'PARTIAL_EXISTING_EVIDENCE_REVIEW_NOT_A_FINAL_PASS','reviewer':'/root/review_upstream_reflection','review_script':{'path':str(Path(__file__).resolve()),'sha256':digest(Path(__file__).read_bytes())},'pipeline_snapshot':{'original_path':str(a.pipeline),'sha256':snapshot_hash,'status':state['status']},'selected_record_sha256_by_module':record_hashes,'selected_records':records,'complete102_gate_satisfied':a.require_complete,'reviewed_selected_modules':len(records),'remaining_selected_modules':102-len(records),'mathematical_scope':{'nodes':6459,'leaves':6460,'guard_cases':8391,'depth':34,'cuts':233,'joins':232,'units':102,'probes':468,'callers':468,'independently_parsed_actual_tree':True,'all_frontier_paths_and_both_children_verified':True,'all_cut_join_statements_and_typed_callers_verified':True,'final_statement':'allSites SitePrefix246.checkSite [] ActualTree254.tree = true','walk_scope':'Every finite PC list, with original consume zero-padding behavior; no clean-PC restriction.','not_asserted':'Binary calibration and internal PA consistency equivalence.'},'actual_guards':actual_guards,'axiom_set_counts':dict(totals),'warning_counts_by_module':warnings,'source_seconds_sum':sum(source_seconds),'source_seconds_max':max(source_seconds,default=0),'audit_seconds_sum':sum(audit_seconds),'hash_binding_checks':checks,'distinct_input_paths':len(bindings),'distinct_resolved_files':len(physical),'current_input_bindings':bindings,'input_resolutions':path_targets,'pipeline_history':history,'attempt_history':attempts,'recovery_review_sha256':RECOVERY,'complete_final_current_rehash':a.require_complete,'compiler_invoked':False,'guard_or_supplied_checker_invoked':False,'version_queried':False,'dependency_build':False,'maintained_files_changed':False,'execution_scope':'Reviewer-owned literal parsing, JSON metadata inspection and current-file hashing only; no proof replay.'}
 if a.require_complete:result['coverage_final_verification_sha256']=record_hashes['BusyBeaver.ZFC.SitesPrefix246']
 (O/'review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'review':str(O/'review.json'),'sha256':digest((O/'review.json').read_bytes()),'status':result['status'],'modules':len(records),'distinct_inputs':len(bindings),'physical_files':len(physical)},indent=2))
if __name__=='__main__':main()
