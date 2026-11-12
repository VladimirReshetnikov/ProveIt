from pathlib import Path
import json,hashlib,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelMap87To88.lean').read_text()
for t in ('OmegaGtF87Draft.omega_gt_F','ConditionalMap87To88Draft.positive_map','hbeta46 : 46≤beta','hMC : MC<beta','P87ShiftedGuard.graph p','P88QuotientGuarded.graph p'):assert t in s
for name in ('ordinary14-87-omega-gt-f-draft','ordinary14-87-to-88-conditional-map-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source map composition and dependency receipts; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelMap87To88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
