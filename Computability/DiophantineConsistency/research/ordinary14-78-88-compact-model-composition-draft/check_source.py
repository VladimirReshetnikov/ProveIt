from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Compact78To88.lean').read_text()
for t in ('Compact78To87Draft.positive_zero_iff K','CompactEquivalence8788Draft.positive_zero_iff K','P78AuxRoot.graph','P88QuotientGuarded.graph','ports CompactFixedBeta.betaNat K lowNat highNat'):assert t in s
for name in ('ordinary14-78-87-compact-model-composition-draft','ordinary14-87-88-compact-model-equivalence-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'symbolic same-port source iff composition, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'Compact78To88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
