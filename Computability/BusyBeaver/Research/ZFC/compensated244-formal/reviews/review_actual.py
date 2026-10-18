#!/usr/bin/env python3
"""Own existing-record reviewer; no compiler/guard/checker execution."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
def load(p):return json.loads(Path(p).read_text())
for key,base,run,np,nc,role,prefix in [
 ('positive-block','/tmp/zfc244-positive-blocks','run2',4,4,'Independent mathematical/source/repair and actual-evidence reviewer; no source, audit or guard authorship.','SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation.'),
 ('original245-invariant','/tmp/zfc244-routing245-invariant','run1',5,8,'Invariant source/audit author reviewing root-executed evidence; this is not an independent proof-author review. Guard and execution were root-owned.','SetTheory.BusyBeaver.ZFC.Routing245Invariant.')]:
 B=Path(base);P=B/run/'verification.json';r=load(P);checks=[]
 def check(ok,label):
  assert ok,(key,label)
  checks.append(label)
 check(r['status']=='PASS' and not r['prepare_only'],'actual terminalPASS')
 check((r['named_axiom_probes'],r['callers'],r['warnings'])==(np,nc,0),'exactcensus andzero warnings')
 check(r['before']==r['after'] and r['all_input_provider_postchecks'],'complete before/after equality')
 for path,h in r['before'].items():check(sha(path)==h,'currentinput '+path)
 for k in ['source','audit']:
  check(sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256'],k+' current/snapshot')
 check(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and not r['global_option_overrides'],'defaultlimits')
 check(not r['compiler_version_query_performed'] and not r['dependency_build'] and not r['downloads'],'no version/build/download')
 check([x['label'] for x in r['commands']]==['source','audit'],'two sequential commands')
 for i,c in enumerate(r['commands']):
  check(c['exit_code']==0 and not c['timed_out'] and c.get('interrupted') is None,'command success '+str(i))
  check(Path(c['log']).read_text()==c['output'] and sha(c['log'])==c['log_sha256'],'rawlog '+str(i))
  check(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'],'resource flags '+str(i))
  check(c['command'][-1]==r[['source','audit'][i]]['snapshot'],'selected source '+str(i))
  check('warning:' not in c['output'] and 'sorryAx' not in c['output'],'output exclusions '+str(i))
 check(sum(c['seconds'] for c in r['commands'])<120,'combined measuredtime bound')
 check(r['source_object_recorded_before_audit'] and r['all_fresh_objects_unchanged_after_audit'],'preaudit/postaudit claims')
 check(len(r['fresh_modules'])==1,'single fresh module')
 fresh=r['fresh_modules'][0];capture=r['source_pass_object'];first=r['fresh_first_provider_before_audit']
 check(capture==dict(fresh,source_command_index=0),'source capture fields')
 check(first=={k:fresh[k] for k in ['module','path','sha256']},'fresh first capture')
 check(sha(fresh['path'])==fresh['sha256'] and fresh['source_sha256']==r['source']['sha256'],'current fresh object')
 check(r['commands'][0]['command'][-3:-1]==['-o',fresh['path']],'source output object command')
 for q in r['reused_modules']:
  check(sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256'],'currentpair '+q['module'])
 projects={q['module']:q for q in r['reused_modules']};seen=set();tools={'Init'}
 def visit(m):
  if m not in projects:tools.add(m);return
  if m in seen:return
  seen.add(m)
  for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):visit(n)
 for m in re.findall(r'^import\s+(\S+)\s*$',Path(r['source']['path']).read_text(),re.M):visit(m)
 check(seen==set(projects)==set(r['exact_project_import_closure']) and len(seen)==2,'exacttwo-projectDFS')
 check(tools=={q['module'] for q in r['toolchain_providers']},'toolboundaryDFS')
 roots=[Path(r['LEAN_PATH']),Path(r['compiler']['path']).parent.parent/'lib/lean']
 for q in r['actual_first_providers']:
  candidates=[root/Path(q['module'].replace('.','/')).with_suffix('.olean') for root in roots]
  actual=next(x.resolve() for x in candidates if x.is_file())
  check(actual==Path(q['actual_first']).resolve() and sha(actual)==q['sha256'],'actualfirst '+q['module'])
 candidates=[root/Path(fresh['module'].replace('.','/')).with_suffix('.olean') for root in roots]
 check(next(x.resolve() for x in candidates if x.is_file())==Path(fresh['path']).resolve(),'target fresh first provider')
 for e in r['provider_evidence']:
  check(sha(e['path'])==e['sha256'],'parent record pin');parent=load(e['path'])
  for m,q in projects.items():check(q==next(z for z in parent['reused_modules'] if z['module']==m),'selected parentpair '+m)
 audit=Path(r['audit']['path']).read_text();names=re.findall(r'^#print axioms (\S+)$',audit,re.M)
 names=[n if n.startswith('SetTheory.') else prefix+n for n in names]
 raw=re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]",r['commands'][1]['output'],re.M)
 parsed=[{'name':n,'axioms':sorted(x.strip() for x in a.split(',') if x.strip())} for n,a in raw]
 check([q['name'] for q in parsed]==names and len(names)==np,'raw reports exactly match audit')
 check(parsed==r['axiom_reports'] and all(q['axioms']==['Quot.sound','propext'] for q in parsed),'exact standardaxiomsets')
 check(len(re.findall(r'^example\b',audit,re.M))==nc,'compiledtypedcaller census')
 history=[]
 if key=='positive-block':
  for path in [B/'review/independent-audit-repair-review.json',B/'run1/verification.json',B/'prepared1/verification.json',B/'prepared2/verification.json']:
   history.append(d(path))
  check(load(B/'run1/verification.json')['status']=='FAIL','earlier auditcensus failure retained')
 result={'status':'EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS','findings':[],'reviewer_role':role,'reviewer_source':d(Path(__file__)),
  'verification':d(P),'source':d(r['source']['path']),'audit':d(r['audit']['path']),'guard':d(B/'check.py'),'boundary':d(r['boundary']['path']),
  'scope':r['scope'],'counts':{'inputs':len(r['before']),'projects':2,'probes':np,'callers':nc,'warnings':0},
  'timings':{c['label']:c['seconds'] for c in r['commands']},'actual_axiom_sets':[q['axioms'] for q in parsed],
  'fresh_object':fresh,'history':history,'parent_scope':r['parent_scope'],
  'supplied_execution':False,'scope_limit':'Only selected existing records, source/object providers and current bytes revalidated; no851-provider ancestor rebuild, no concrete244 endpoint or PA internalization claimed.',
  'checks':checks,'check_count':len(checks)}
 out=OUT/(key+'-actual-review.json');out.write_text(json.dumps(result,indent=2)+'\n');print(d(out))
