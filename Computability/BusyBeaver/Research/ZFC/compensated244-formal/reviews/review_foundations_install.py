#!/usr/bin/env python3
"""Own read-only installed/default metadata review; never imports a supplied guard."""
from pathlib import Path
import hashlib,json,re,difflib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=R/'Computability/BusyBeaver/Research/ZFC';O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p))
load=lambda p:json.loads(Path(p).read_text())
checks=[]
def check(x,s):
 assert x,s
 checks.append(s)
M=Path('/tmp/zfc244-foundations-published-paths.json');rows=load(M);check(len(rows)==92,'92 mapped files')
for q in rows:
 p=R/q['path'];check(sha(p)==q['sha256'],'installed '+q['path'])
 if q['origin'].startswith('/'):check(p.read_bytes()==Path(q['origin']).read_bytes(),'exact original '+q['path'])
 check(p.suffix not in ['.olean','.ilean'] and '/cache/' not in str(p),'no cache/object '+q['path'])
preps=[]
for key,base,slug,mod,auditname,guardname,run in [
 ('generic','/tmp/zfc244-positive-blocks','positive-blocks','PositiveBlockBisimulation','positive_block_bisimulation_audit.lean','check_positive_block_bisimulation.py','run2'),
 ('invariant','/tmp/zfc244-routing245-invariant','invariant','Routing245Invariant','routing245_invariant_audit.lean','check_routing245_invariant.py','run1'),
 ('table','/tmp/zfc244-compensated-lean/table','table','TableCompensated244','table_compensated244_audit.lean','check_table_compensated244.py','run1')]:
 B=Path(base);guard=D/guardname;old=(B/'check.py').read_text();new=guard.read_text()
 expected=old.replace(f"HERE=Path('{base}')","HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]")
 expected=expected.replace(f"default=HERE/'{mod}.lean'",f"default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/{mod}.lean'")
 expected=expected.replace("default=HERE/'Audit.lean'",f"default=HERE/'{auditname}'")
 expected=expected.replace("default=HERE/'boundary.json'",f"default=HERE/'compensated244-formal/{slug}/boundary.json'")
 check(expected==new,key+' exact four default adaptations only')
 delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='actual-executed-check.py',tofile='maintained-check.py'))
 check(delta==(D/f'compensated244-formal/{slug}/publication-defaults.diff').read_text(),key+' exact published diff')
 p=Path('/tmp/zfc244-maintained-prepare')/key/'verification.json';r=load(p);actual=load(B/run/'verification.json')
 check(r['status']=='PREPARED_NOT_BUILT' and r['prepare_only'] and r['commands']==r['fresh_modules']==[],key+' unbuilt preparation')
 check(r['before']==r['after'] and r['all_input_provider_postchecks'],key+' before/after')
 for x,h in r['before'].items():check(sha(x)==h,key+' current input '+x)
 check(r['source']['path']==str(R/f'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/{mod}.lean') and r['audit']['path']==str(D/auditname),key+' maintained source/audit selection')
 for k in ['source','audit']:check(sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256']==actual[k]['sha256'],key+' source/audit exact actual '+k)
 check(r['boundary']['path']==str(D/f'compensated244-formal/{slug}/boundary.json') and r['boundary']['sha256']==actual['boundary']['sha256'],key+' maintained boundary same bytes')
 check(r['reused_modules']==actual['reused_modules'] and r['toolchain_providers']==actual['toolchain_providers'],key+' exact actual providers')
 check(len(r['reused_modules'])==2 and r['exact_project_import_closure']==actual['exact_project_import_closure'],key+' narrow closure')
 check(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and not r['global_option_overrides'],key+' resource limits')
 check(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),key+' no version/build/download')
 for q in r['actual_first_providers']:check(sha(q['actual_first'])==q['sha256'],key+' actual first '+q['module'])
 preps.append(d(p))
doc=D/'compensated244_foundations.md';text=doc.read_text()
for target in re.findall(r'\]\(([^)]+)\)',text):
 if '://' not in target:check((doc.parent/target.split('#')[0]).exists(),'doc link '+target)
check('4 / 4' in text and '5 / 8' in text and '53 / 6' in text,'document exact 62/18 census')
check('finite-support' in text and 'Internal PA formalization remains' in text and '851-module' in text,'scope and boundary explicit')
receipt=dict(status='INSTALLED_FOUNDATIONS_AND_DEFAULT_PREPARATION_REVIEW_PASS',findings=[],reviewer_source=d(__file__),reviewer_role='Independent publication/default reviewer; invariant proof-source/audit author, disclosed separately in original evidence receipt. Not publisher or executor.',map=d(M),document=d(doc),preparations=preps,counts=dict(mapped_files=92,actual_probes=62,actual_callers=18,prepared_inputs=[16,15,22],proof_commands=0,fresh_modules=0),scope='Exact mapped foundation artifacts, original failed generic attempt, four-only default path adaptations, current installed bytes and three unbuilt default preparations. No new execution, broad ancestor replay or concrete global244 endpoint claim.',checks=checks,check_count=len(checks))
p=O/'foundations-installed-default-review.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(d(p))
