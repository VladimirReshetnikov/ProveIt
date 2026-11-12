from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Parent88Equivalence.lean').read_text()
for t in ('ModelMapParentTo88Draft.positive_map','ModelMap88ToParentDraft.positive_map','P72Root.cast_port p 0','P88FourSquare.graph','P88QuotientGuarded.graph','hb : 0<(p 0:V)'):assert t in s
for name in ('ordinary13-parent-to-88-model-map-draft','ordinary14-88-to-parent-model-map-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'natural-port source iff and map receipts; no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'Parent88Equivalence.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
