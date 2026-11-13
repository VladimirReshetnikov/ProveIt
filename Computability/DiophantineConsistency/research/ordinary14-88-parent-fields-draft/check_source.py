from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentFields88.lean').read_text()
for t in ('P88QuotientGuarded.output_shape','fiveSquares_eq_zero_iff','Ring88ToParentDraft.main_eval','Ring88ToParentDraft.aux_eval','Ring88ToParentDraft.strong_eval','P88QuotientGuarded.graph p'):assert t in s
for name in ('ordinary14-88-guard-draft','ordinary14-88-parent-ring-client-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'88 nonfirst field source composition and DAG receipts; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ParentFields88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
