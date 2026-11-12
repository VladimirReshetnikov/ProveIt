from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelMap88ToParent.lean').read_text()
for t in ('FirstRootGap88Draft.quotient_and_root_gap','FreshParentRootDraft.fresh_root','ParentFirst88Draft.first_zero','ParentFields88Draft.projected_fields','P88FourSquare.output_shape','parent_positive','cast_parent'):assert t in s
for name in ('ordinary14-88-first-root-gap-draft','ordinary14-fresh-parent-root-draft','ordinary14-88-parent-first-draft','ordinary14-88-parent-fields-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source map and dependency receipts, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelMap88ToParent.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
