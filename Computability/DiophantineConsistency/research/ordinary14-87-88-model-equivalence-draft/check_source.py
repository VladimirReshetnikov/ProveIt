from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelEquivalence8788.lean').read_text()
for t in ('ModelMap87To88Draft.positive_map','PositiveMap88To87Draft.positive_map','P87ShiftedGuard.graph p','P88QuotientGuarded.graph p','hbeta46 : 46≤beta','hMC : MC<beta'):assert t in s
for name in ('ordinary14-87-to-88-model-map-draft','ordinary14-88-to-87-positive-map-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source iff and dependency receipts; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelEquivalence8788.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
