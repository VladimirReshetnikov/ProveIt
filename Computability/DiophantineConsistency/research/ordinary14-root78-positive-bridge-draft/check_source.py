from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Root78PositiveBridge.lean').read_text()
for t in ('Compact78To88Draft.positive_zero_iff','Quotient88PositiveBridgeDraft.positiveBridge','paramKernel rho','P78AuxRoot.graph CompactSymbolicModelIff.p','hpair.trans'):assert t in s
for name in ('ordinary14-78-88-compact-model-composition-draft','ordinary14-quotient88-positive-bridge-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'symbolic 78 positive bridge source composition, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'Root78PositiveBridge.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
