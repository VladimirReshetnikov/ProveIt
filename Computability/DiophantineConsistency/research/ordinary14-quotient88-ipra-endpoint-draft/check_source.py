from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Quotient88Endpoint.lean').read_text()
for t in ('native_of_positive _ Quotient88PositiveBridgeDraft.positiveBridge','standard_of_positive _ Quotient88PositiveBridgeDraft.positiveBridge','reference_of_positive _ Quotient88PositiveBridgeDraft.positiveBridge','positiveShift Quotient88PositiveBridgeDraft.expression'):assert t in s
r=D/'research/ordinary14-quotient88-positive-bridge-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source adapter inventory and bridge receipt; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'Quotient88Endpoint.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
