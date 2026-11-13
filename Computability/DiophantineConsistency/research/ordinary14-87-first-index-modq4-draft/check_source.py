from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'FirstIndexModQ487.lean').read_text()
for t in ('FirstIndex87Draft.index_residues','Q4Rank87Draft.q4_rank','magnitude_mod','4*(v 6)*qq^2*(s*s)*w','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-first-index-draft','ordinary14-87-q4-rank-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q in range(2,12):
 for X in range(1,9):
  for s0 in range(1,6):
   Y=q**3*s0;m=X*Y*Y
   for w in range(5):
    assert (4*m*w)%q**4==0
    count+=1
print(json.dumps({'multiple_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstIndexModQ487.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
