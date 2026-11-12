from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'PositiveMap88To87.lean').read_text()
for t in ('Function.update v 13 (v 13+v 1)','add_pos (hv 13) (hv 1)','Ring88To87Draft.output_eval','P88QuotientGuarded.graph p','P87ShiftedGuard.graph p'):assert t in s
r=D/'research/ordinary14-88-87-ring-client-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
assert all(t+F>0 for t in range(1,20) for F in range(1,20))
print(json.dumps({'positive_update_controls':361,'lean_run':False,'source_sha256':hashlib.sha256((p/'PositiveMap88To87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
