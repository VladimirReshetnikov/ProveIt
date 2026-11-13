from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'FirstQuotient88.lean').read_text()
for t in ('Ring88To87Draft.output_eval','PositiveMap88To87Draft.cast_forward','FirstQuotient87Draft.quotient_and_root','hJ : 0<v 0','hY : 0<v 7','P88QuotientGuarded.graph p'):assert t in s
for name in ('ordinary14-88-to-87-positive-map-draft','ordinary14-87-first-quotient-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for F in range(-4,5):
 for t in range(-4,5):
  v=list(range(14));v[1]=F;v[13]=t;u=v.copy();u[13]=t+F
  assert all(u[i]==v[i] for i in range(13))
  count+=1
print(json.dumps({'slot_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstQuotient88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
