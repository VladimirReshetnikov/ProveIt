"""Owned actual readback of one successful compiler call; no recompilation."""
from pathlib import Path
import hashlib,json,re
D=Path('/tmp/k215-decrement-prefix-component-check-v1')
E=Path('/tmp/k215-decrement-prefix-execution')
OUT=Path('/tmp/k215-decrement-prefix-component-readback-v1.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
assert not OUT.exists()
record=read(D/'record.json');before=read(D/'before.json');outer=read(E/'component-job-outer.json')
assert outer['status']=='FAIL' and outer['exit_code']==1
assert sha(E/'component-job.stderr')==outer['stderr_sha256']=='e7d2b08e10b06b678c2087721aca6f5d6deea69d305dc3dc3e2c8c7dc8579c16'
assert sha(E/'component-job.stdout')==outer['stdout_sha256']
assert record['status']=='PASS' and record['exit_code']==0 and not record['timed_out']
assert record['checker_sha256']==sha('/tmp/k215-decrement-prefix-component-check-v2.py')=='77eac42c2223ae7c508fafbf558a372c6bbf5c84a4b89d680b9d6389befb81ba'
assert record['source_sha256']==sha(record['source'])==before['component_source_sha256']=='d5cdf19ed390b4eec9302ff78790b939d37a612a6bcd34b79d30e84208f458f6'
assert sha(D/'compiler.log')==record['log_sha256']=='49a60e1733a66a55d03d0212316256353a0b933cad6e361b61b151c5c87e55ec'
text=(D/'compiler.log').read_text();assert not any(x in text for x in ['warning:','error:','sorryAx'])
name='SetTheory.BusyBeaver.ZFC.DecrementPrefixNextLead.neutral_prefix_compose'
assert re.fullmatch("'"+re.escape(name)+r"' depends on axioms: \[\s*propext,\s*Classical\.choice,\s*Quot\.sound\s*\]\s*",text)
for path,h in before['bindings'].items():assert sha(path)==h,path
basis=Path('/tmp/k215-phase24-check-v3/candidate-build-run1');basis_result=read(basis/'result.json')
assert sha(basis/'completed.json')==basis_result['completed_sha256']
report={'status':'PASS_DETACHED_COMPONENT_ACTUAL_READBACK','source_sha256':record['source_sha256'],'object_sha256':sha(D/'NeutralPrefixCompose.olean'),'log_sha256':sha(D/'compiler.log'),'record_sha256':sha(D/'record.json'),'before_sha256':sha(D/'before.json'),'original_control_outer_sha256':sha(E/'component-job-outer.json'),'reader_sha256':sha(__file__),'seconds':record['seconds'],'warnings':0,'axiom_profile':['propext','Classical.choice','Quot.sound'],'dependency_modules':len(before['dependency_modules']),'input_files_postchecked':len(before['bindings']),'production_changes':0,'original_control_status':'FAIL_AFTER_SUCCESSFUL_COMPILATION_EXPECTED_SINGLE_LINE_PROFILE_BUT_LEAN_WRAPPED_LINES','scope':'One owned neutral-prefix composition theorem compiled successfully. Readback accepts only the exact theorem name and exact ordered three-axiom profile with whitespace allowed at commas. No compiler rerun, rule weakening, paired checker, site certificate, endpoint or speed claim. All original bytes/failed control receipt retained; phase24 evidence unchanged.'}
with OUT.open('x') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps(report))
