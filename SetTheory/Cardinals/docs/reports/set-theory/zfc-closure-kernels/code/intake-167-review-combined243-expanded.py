#!/usr/bin/env python3
"""Read/hash existing expanded evidence only. No supplied import or execution."""
from pathlib import Path
import json,hashlib,re
B=Path('/tmp/zfc243-root-replay');C=B/'candidate';O=B/'independent-review';checks=[]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
def load(p):return json.loads(Path(p).read_text())
def check(x,label):
 assert x,label
 checks.append(label)
v=load(B/'expanded-verification.json');ex=load(B/'expanded-execution.json');r=load(C/'expanded-runtime.json');quick=load(O/'quick-review.json')
check(v['status']=='PASS_COMBINED243_EXPANDED_RUNTIME' and v['commands']==ex and len(ex)==1,'terminal existing expanded command')
check(v['before']==v['after']==load(B/'quick-verification.json')['before'] and len(v['before'])==9,'nine tracked identities stable across runs')
for p,h in v['before'].items():check(sha(p)==h,'current tracked '+p)
for q in quick['current_reference_files']:check(sha(q['path'])==q['sha256'],'current delivered reference '+q['path'])
c=ex[0];check(c['job']=='expanded' and c['exit_code']==0 and c['timeout'] is False and 0<c['seconds']<600,'actual command exits within bound')
check(c['command']==['/home/codex/.local/bin/python3','-B',str(B/'adapters/check_runtime_combined243.py'),'--reference','/tmp/zfc244-rotation-root-replay/copy/reference/baseline245','--candidate',str(C),'--expanded'],'exact full mode command without reduced bounds')
check((B/'expanded.stderr.log').read_bytes()==b'','empty stderr')
stdout=(B/'expanded.stdout.log').read_text();payload=json.loads(stdout[stdout.index('{\n'):]);check(payload=={k:v for k,v in r.items() if k not in ['cases','literal_rows']},'raw stdout agrees full result summary')
check('FAIL_CASE' not in stdout and 'Traceback' not in stdout,'no error text')
check(r['status']=='PASS_UNIVERSAL_EXPANDED_RUNTIME' and r['complete'] and r['source_leaves']==6459 and r['expected_cases']==8390,'complete all-source scope')
check(r['counts']==v['counts']==dict(cases=8390,symbolic_rules=2314868),'exact census')
check(r['frame_padding']==64 and r['arbitrary_primary_registers'] and r['arbitrary_nonempty_finite_spare_suffix'] and r['positive_progress_checked'],'whole-frame all-values scope')
check(r['table_sha256']==sha(C/'machine_old.tm') and r['sites_logical_sha256']==sha(C/'sites_logical.json'),'actual table/source identity')
logical=load(C/'sites_logical.json');signatures=[(i,p,op,reg,z) for i,(p,op,reg) in enumerate(logical) for z in ([True,False] if op=='CD' else [None])]
check(len(signatures)==len(r['cases'])==8390,'all logical guard cases')
for row,sig in zip(r['cases'],signatures):
 check(tuple(row[k] for k in ['index','pc','op','r','zero'])==sig,'exact source guard '+str(sig[0])+':'+str(sig[4]))
 terms=row['cost'].split('+');check(terms[0].isdigit() and int(terms[0])==row['time_lower_bound']>=1,'positive time constant '+str(sig))
 check(all(re.fullmatch(r'[1-9][0-9]*\*(?:gap|r[0-8]|spare_first|width_spare_tail)',x) for x in terms[1:]),'nonnegative arbitrary-variable coefficients '+str(sig))
 check(0<row['rules']<3000,'default symbolic fuel bound '+str(sig))
 check(row['motion'] in (['13'] if row['op']=='CH' else ['0','-1']),'head motion '+str(sig))
check(min(q['time_lower_bound'] for q in r['cases'])==13,'minimum progress13')
check(sum(q['rules'] for q in r['cases'])==sum(r['rules'].values())==2314868,'rules total consistency')
check(r['rules']=={'literal':1987184,'unary-induction':322484,'finite-list-induction':5200},'exact rule categories')
rows=[tuple(q) for q in r['literal_rows']];check(len(rows)==len(set(rows))==r['literal_rows_covered']==485,'literal row census')
blank=load(B/'blank/independent-blank.json');oldlabels=set(load(C/'renumbering.json')['old_to_new']) if False else None
# Parse table rows without executing the machine or a delivered parser.
text=(C/'machine_old.tm').read_text();table=set()
for line in text.splitlines():
 m=re.match(r'^\s*(\d+)\s+([01])\s+',line)
 if m:table.add((int(m[1]),int(m[2])))
check(len(table)==486 and set(rows)<=table and table-set(rows)=={(27,1)},'covered/unused exact literal rows')
check(r['unused_rows']==v['unused_rows']==[[27,1]] and v['rows_covered']==485,'retained unused completion row')
check(r['seconds']<c['seconds'] and 0<r['seconds']<600,'internal timing bounded by root timing')
record=dict(status='EXISTING_EXPANDED_REPLAY_EVIDENCE_REVIEW_PASS',findings=[],verification=d(B/'expanded-verification.json'),execution=d(B/'expanded-execution.json'),result=d(C/'expanded-runtime.json'),logs=[d(B/'expanded.stdout.log'),d(B/'expanded.stderr.log')],reviewer_source=d(__file__),prior_quick_review=d(O/'quick-review.json'),tracked_inputs=v['before'],checks=len(checks),results=dict(cases=8390,symbolic_rules=2314868,rows=485,unused_row=[27,1],source_leaves=6459,minimum_time_constant=13,root_seconds=c['seconds'],rules=r['rules']),input_scope='Nine actual before/after/current tracked identities. All reference files from the prior independent current-pristine comparison were rehashed again. The root runner does not record historical before/after hashes for the full inherited reference tree; this review does not invent that capture.',source_review='Read complete root runner, complete runtime adapter and inherited expanded case/step implementation. Adapter installs the exact candidate table, re-proves block/word rules, then invokes every logical leaf and both decrement branches with nine arbitrary naturals, gap>=64 and arbitrary nonempty finite spare suffix. No reduced limit or interval specialization selected.',limits='Root600s wall-clock bound; inherited3000 symbolic-rule per-case limit unchanged. Existing ordinary symbolic induction evidence, not kernel replay or a new PA proof.',reviewer_role='Independent adapter/existing-evidence reviewer; author of separate Lean ports and guards. Did not author adapters, root runner or actual replay.',supplied_execution=False)
(O/'expanded-review.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'review':d(O/'expanded-review.json'),'checks':len(checks)},indent=2))
