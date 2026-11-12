from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'CompactEquivalence8687.lean').read_text()
for t in ('ModelEquivalence8687Draft.positive_zero_iff','C44Short15Facts.port_bounds','CompactFixedBeta.beta_identity','P72Root.cast_port p 0','P72Root.cast_port p 3','P86ResidueGraph.graph','P87ShiftedGuard.graph'):assert t in s
r=D/'research/ordinary14-86-87-model-equivalence-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'symbolic port source specialization and draft replay; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'CompactEquivalence8687.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
