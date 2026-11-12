from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'AuxNorm87.lean').read_text()
for t in ('FourFields87Draft.fields_of_zero','NaturalRank87Draft.rank_of_87_zero','P86ResidueGraph.graph p','P87ShiftedGuard.graph p','P72Aux.ι_absdiff_sq'):assert t in s
for name in ('ordinary14-87-four-fields-draft','ordinary14-87-natural-rank-draft','ordinary14-87-strong-norm-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for Vp in range(8):
 for Vn in range(8):
  for u in range(1,6):
   for Q in range(5):
    z=Vp-Vn;A=(z+u)**2-Q*((z+u)**2-z*z)
    L=Q*abs(Vp-Vn)**2+abs(Vp+u-Vn)**2
    R=1+Q*abs(Vp+u-Vn)**2
    assert (A==1)==(L==R)
    count+=1
print(json.dumps({'signed_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'AuxNorm87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
