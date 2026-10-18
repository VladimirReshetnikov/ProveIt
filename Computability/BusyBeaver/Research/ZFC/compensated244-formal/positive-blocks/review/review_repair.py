#!/usr/bin/env python3
"""Own metadata and source-delta review; never imports or invokes the guard."""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc244-positive-blocks');H=B/'history/run1-ambiguous-axiom-name'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return {'path':str(p),'sha256':sha(p)}
def load(p):return json.loads(Path(p).read_text())
checks=[]
def check(ok,label):
 assert ok,label
 checks.append(label)
old=(H/'Audit.lean').read_text();new=(B/'Audit.lean').read_text()
prefix='SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation.'
check(re.sub(r'^#print axioms (\S+)$',lambda m:'#print axioms '+prefix+m[1],old,flags=re.M)==new,'exact four-name qualification; clients unchanged')
og=(H/'check.py').read_text();ng=(B/'check.py').read_text()
expected=og.replace(sha(H/'Audit.lean'),sha(B/'Audit.lean')).replace("==PROBES,'Audit short names changed.'","==[PREFIX+n for n in PROBES],'Audit qualified names changed.'")
check(expected==ng,'guard changes only audit pin and qualified-name preflight')
aliases={str(B/'Audit.lean'):H/'Audit.lean',str(B/'check.py'):H/'check.py'}
record_bindings=[]
for name in ['prepared1','run1','prepared2']:
 p=B/name/'verification.json';r=load(p)
 check(r['before']==r['after'] and r['all_input_provider_postchecks'],name+' complete postchecks')
 for path,h in r['before'].items():
  q=aliases.get(path,Path(path)) if name!='prepared2' else Path(path)
  check(sha(q)==h,name+' input '+path)
 check(r['source']['sha256']==sha(B/'PositiveBlockBisimulation.lean'),name+' unchanged source')
 check(r['source']['sha256']==sha(r['source']['snapshot']),name+' source snapshot')
 check(r['audit']['sha256']==sha(r['audit']['snapshot']),name+' audit snapshot')
 check(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],name+' same limits')
 check(not r['compiler_version_query_performed'] and not r['dependency_build'] and not r['downloads'],name+' no version/build/download')
 for q in r['actual_first_providers']:
  check(sha(q['actual_first'])==q['sha256'],name+' current first provider '+q['module'])
 if name.startswith('prepared'):
  check(r['status']=='PREPARED_NOT_BUILT' and r['commands']==[] and r['fresh_modules']==[],name+' no proof commands')
 else:
  check(r['status']=='FAIL' and r['error']=="RuntimeError('Wrong actual reports.')",'original exact guard rejection')
  check([q['label'] for q in r['commands']]==['source','audit'] and all(q['exit_code']==0 and not q['timed_out'] for q in r['commands']),'both original compiler commands exited0')
  for q in r['commands']:
   check(sha(q['log'])==q['log_sha256'] and Path(q['log']).read_text()==q['output'],'raw '+q['label']+' log')
  names=re.findall(r"^'([^']+)' depends on axioms:",r['commands'][1]['output'],re.M)
  check(names==[prefix+'Simulation.symm',prefix+'forward','SetTheory.BusyBeaver.ZFC.RuntimePerm252.halts_iff',prefix+'halts_iff',prefix+'blank_halts_iff'],'five exact reports including ambiguous old halts_iff')
  check(not any('warning:' in q['output'] for q in r['commands']),'original zero warnings')
  fresh=r['fresh_modules'][0]
  check(r['source_object_recorded_before_audit'] and sha(fresh['path'])==fresh['sha256'],'original fresh object remains captured')
 record_bindings.append(desc(p))
prep=load(B/'prepared2/verification.json')
projects={q['module']:q for q in prep['reused_modules']}
seen=set();external={'Init'}
def visit(m):
 if m not in projects:external.add(m);return
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):visit(n)
visit('BusyBeaver.ZFC.RuntimePerm252')
check(seen==set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.RuntimePerm252'},'independent two-project DFS')
check(external=={'Init','Lean.Elab.Tactic.Omega'},'explicit tool boundaries')
parent=load(prep['provider_evidence'][0]['path'])
for m,q in projects.items():check(q==next(x for x in parent['reused_modules'] if x['module']==m),'exact selected parent pair '+m)
result={'status':'AUDIT_QUALIFICATION_REPAIR_AND_PREPARATION_REVIEW_PASS','findings':[],
 'reviewer_source':desc(Path(__file__)),'source':desc(B/'PositiveBlockBisimulation.lean'),'audit':desc(B/'Audit.lean'),'guard':desc(B/'check.py'),
 'reviewer_role':'Independent source/API reviewer of the generic root-authored lemma and repair; no guard/compiler execution or authorship.',
 'records':record_bindings,'history_aliases':{k:desc(v) for k,v in aliases.items()},
 'assessment':['Only the four #print axiom names are fully qualified. The proof source and all four typed caller bodies/statements remain byte-identical.',
 'Original source and audit compilation exited0, but five actual reports made the guard reject. This is retained as whole-unit FAIL; it is not relabeled PASS.',
 'Qualified audit preflight and its SHA are the only guard changes. All resource limits and source-before-audit logic remain unchanged.',
 'The selected two-project closure is rehashed and tied to the existing BinaryRouting245 record. Other851-provider ancestor imports are provenance, not revalidated by this narrow review.',
 'Prepared2 is unbuilt with empty commands/fresh modules. An actual repaired-run receipt will be separate.'],
 'checks':checks,'check_count':len(checks),'supplied_execution':False}
(B/'review/independent-audit-repair-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(desc(B/'review/independent-audit-repair-review.json'))
