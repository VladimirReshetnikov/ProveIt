from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelMapParentTo88.lean').read_text()
for t in ('ParentTransportQuotientsDraft.quotient_bundle','ParentFourFieldsDraft.fields_of_zero','ParentTo88GuardDraft.guard_of_balance','ParentTo88FirstDraft.first_zero','P88QuotientGuarded.output_shape','target_positive','cast_target'):assert t in s
for name in ('ordinary13-parent-transport-quotients-draft','ordinary13-parent-four-fields-draft','ordinary13-parent-to-88-guard-draft','ordinary13-parent-to-88-first-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'same-parent-zero positive target source composition; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelMapParentTo88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
