from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelEquivalence8687.lean').read_text()
for t in ('PositiveMap86To87Draft.positive_map','ModelMap87To86Draft.positive_map','P86ResidueGraph.graph p','P87ShiftedGuard.graph p','hbeta46 : 46≤beta','hradix : beta=Exp.exp t-1'):assert t in s
for name in ('ordinary14-86-to-87-positive-map-draft','ordinary14-87-to-86-model-map-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source iff composition and draft receipt replay; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelEquivalence8687.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
