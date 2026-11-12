from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'P72ExactIndices87.lean').read_text()
for t in ('P72FirstInputs87Draft.first_inputs','MainIndex87Draft.main_index','StrongNorm87Draft.strong_norm','AuxNorm87Draft.aux_norm','P72Exact.indices_ordinary qq xx yy kk R d cc aa s','(v 4) (v 3) (v 5) (v 11)','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-p72-first-inputs-draft','ordinary14-87-main-index-draft','ordinary14-87-strong-norm-draft','ordinary14-87-aux-norm-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'P72 source-interface inventory and dependency receipts, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'P72ExactIndices87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
