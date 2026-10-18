#!/usr/bin/env python3
"""Own existing terminal evidence review; never invokes supplied executable code."""
from pathlib import Path
import json,hashlib,re
B=Path('/tmp/zfc244-endpoint');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();d=lambda p:dict(path=str(p),sha256=sha(p));load=lambda p:json.loads(Path(p).read_text())
r=load(B/'run1/verification.json');pre=load(B/'prepared1/verification.json');cfg=load(B/'guard-config.json');checks=[]
def check(x,s):
 assert x,s
 checks.append(s)
check(r['status']=='PASS' and not r['prepare_only'],'terminal actual PASS')
check((r['named_axiom_probes'],r['callers'])==(6,6) and r['warnings']==dict(source=0,audit=0),'6/6 zero warnings')
check(r['before']==r['after'] and r['all_input_provider_postchecks'],'before/after and postchecks')
for p,h in r['before'].items():check(sha(p)==h,'current input '+p)
check(r['reused_modules']==pre['reused_modules'] and r['toolchain_providers']==pre['toolchain_providers'],'same prepared provider selection')
check(r['project_module_count']==857 and r['exact_project_import_closure'] and r['candidate_provider_count']==857 and not r['excluded_candidate_modules'] and not r['external_project_boundaries'],'exact857 closure no exclusions')
projects={q['module']:q for q in r['reused_modules']};seen=set();tools={'Init'}
def visit(m):
 if m not in projects:tools.add(m);return
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):visit(n)
for m in cfg['imports']:visit(m)
check(seen==set(projects)==set(cfg['expected_modules']),'actual independentDFS')
check(tools==set(r['actual_direct_tool_imports'])=={q['module'] for q in r['toolchain_providers']}=={'Init','Lean.Elab.Tactic.Omega'},'exact tool boundary')
for q in r['reused_modules']:
 for k in ['source','object']:check(sha(q[k])==q[k+'_sha256'],'provider '+k+' '+q['module'])
check(r['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults') and r['shared_wall_seconds']==120,'same default proof/resource limits')
check(not any(r[k] for k in ['source_overridden','audit_overridden','compiler_version_query_performed','dependency_build','downloads']),'no overrides/version/build/download')
for k in ['source','audit']:
 check(sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256']==cfg[k+'_sha256'],'exact source/snapshot '+k)
check([c['label'] for c in r['commands']]==['source','audit'],'source then audit')
for i,c in enumerate(r['commands']):
 check(c['exit_code']==0 and not c['timed_out'],'successful command '+c['label'])
 check(Path(c['log']).read_text()==c['output'],'raw log '+c['label'])
 check(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'exact command '+c['label'])
 check(c['cwd']==str(Path(r['audit']['snapshot']).parent),'snapshot cwd '+c['label'])
 check('warning:' not in c['output'] and 'sorryAx' not in c['output'],'diagnostic boundary '+c['label'])
check(sum(c['seconds'] for c in r['commands'])<120,'measured shared budget')
check(len(r['fresh_modules'])==1 and r['source_object_recorded_before_audit'] and r['all_fresh_objects_unchanged_after_audit'],'fresh object assertions')
f=r['fresh_modules'][0];check(r['source_pass_object']==dict(f,source_command_index=0),'exact preaudit source capture')
check(sha(f['path'])==f['sha256'] and f['source_sha256']==r['source']['sha256'],'fresh object current')
cap=r['fresh_first_provider_before_audit'];check(cap==dict(module=f['module'],actual_first=f['path'],resolved=str(Path(f['path']).resolve()),sha256=f['sha256']),'exact preaudit first provider')
roots=[Path(r['LEAN_PATH']),Path(r['compiler']['path']).parent.parent/'lib/lean']
def first(m):return next((p/Path(m.replace('.','/')).with_suffix('.olean')).resolve() for p in roots if (p/Path(m.replace('.','/')).with_suffix('.olean')).is_file())
check(first(f['module'])==Path(f['path']).resolve(),'fresh first after audit')
for q in r['actual_first_providers']:
 check(first(q['module'])==Path(q['resolved']).resolve()==Path(projects[q['module']]['object']).resolve() and sha(first(q['module']))==q['sha256'],'actual first '+q['module'])
for q in r['toolchain_providers']:check(first(q['module'])==Path(q['object']).resolve() and sha(first(q['module']))==q['object_sha256'],'actual tool '+q['module'])
reports=re.findall(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)
parsed=[dict(name=n,axioms=[x.strip() for x in a.split(',') if x.strip()]) for n,a in reports]
audit=Path(r['audit']['path']).read_text();check([q['name'] for q in parsed]==re.findall(r'^#print axioms (\S+)$',audit,re.M),'six exact names')
check(parsed==r['actual_axiom_sets'],'actual exact recorded axiom order')
check([set(q['axioms']) for q in parsed]==[set(),{'propext','Quot.sound'}]+[{'propext','Quot.sound','Classical.choice'}]*4,'exact standard axiom sets')
check(len(re.findall(r'^example\b',audit,re.M))==6,'six compiled typed clients')
for e in r['provider_evidence']:check(sha(e['path'])==e['sha256'],'actual parent pin '+e['path'])
repair=load(O/'endpoint-audit-repair-review.json')
check(sha(repair['historical_audit']['path'])==repair['historical_audit']['sha256'] and sha(repair['audit']['path'])==repair['audit']['sha256'],'unexecuted audit correction preserved')
receipt=dict(status='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS',findings=[],reviewer_source=d(__file__),reviewer_role='Independent endpoint source/API, guard and root-executed evidence reviewer; author of separate Routing245Invariant prerequisite, not endpoint source, audit, guard or execution.',verification=d(B/'run1/verification.json'),source=d(r['source']['path']),audit=d(r['audit']['path']),guard=d(B/'check.py'),preparation=d(B/'prepared1/verification.json'),guard_review=d(O/'endpoint-guard-preparation-review.json'),source_review=d(O/'endpoint-source-review.json'),audit_repair_review=d(O/'endpoint-audit-repair-review.json'),counts=dict(inputs=len(r['before']),projects=857,toolchain_providers=2,probes=6,callers=6,warnings=0),actual_axiom_sets=parsed,fresh_object=f,timings={c['label']:c['seconds'] for c in r['commands']},raw_logs=[d(c['log']) for c in r['commands']],scope=r['scope'],scope_limit='Closed external Lean equivalences for the exact principal compensated244 machine and standard coded ZF/ZFC refutation. No internal PA theorem, unconditional consistency/nonhalting, whole-function-tape semantics, alternative244-machine claim or new proof execution by this reviewer.',supplied_execution=False,checks=checks,check_count=len(checks))
p=O/'endpoint-actual-review.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(d(p));print(receipt['counts'])
