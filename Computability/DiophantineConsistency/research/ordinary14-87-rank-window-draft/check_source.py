from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'RankWindow87.lean').read_text()
for t in ('gap_of_87_zero','scalar_rank_window','scalar_lower40','P87ShiftedGuard.graph p','hMC : MC<beta','hMF : MF<2*beta'):assert t in s
r=D/'research/ordinary14-87-guard-gap-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for beta in range(2,15):
 for J in range(1,5):
  q=beta*J+1
  for F in range(1,q):
   for alpha in range(1,q-F):
    R=((q-1)*(q-F)+alpha)*(q*q-1)
    assert R>=40 and R+q**3+q+1<=q**4
    count+=1
print(json.dumps({'zero_mask_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'RankWindow87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
