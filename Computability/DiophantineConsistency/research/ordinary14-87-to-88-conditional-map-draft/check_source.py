from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ConditionalMap87To88.lean').read_text()
for t in ('v 13-v 1','hstrict : v 1<v 13','P72Root.ι_tsub (le_of_lt hstrict)','Ring88To87Draft.output_eval','P87ShiftedGuard.graph p','P88QuotientGuarded.graph p'):assert t in s
r=D/'research/ordinary14-88-to-87-positive-map-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
assert all(omega-F>0 and omega-F+F==omega for omega in range(2,30) for F in range(1,omega))
print(json.dumps({'strict_update_controls':406,'lean_run':False,'source_sha256':hashlib.sha256((p/'ConditionalMap87To88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
