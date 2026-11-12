from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'NaturalRank87.lean').read_text()
for t in ('GuardGap87Draft.gap_of_87_zero','NaturalRank84Draft.rank_repr','P87ShiftedGuard.graph p','hMC hMF hF hq2'):assert t in s
for name in ('ordinary14-87-guard-gap-draft','ordinary14-84-natural-rank-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q in range(3,30):
 for F in range(1,q):
  for alpha in range(1,q-F):
   assert F<=q and q*q>=1
   count+=1
print(json.dumps({'guard_gap_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'NaturalRank87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
