from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'P72FirstInputs87.lean').read_text()
for t in ('RankWindow87Draft.rank_window','FirstIndexModQ487Draft.first_index_mod_q4','mod_eq_self_of_lt hlt','P87ShiftedGuard.graph p'):assert t in s
for name in ('ordinary14-87-first-index-modq4-draft','ordinary14-87-rank-window-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for modulus in range(2,60):
 for R in range(modulus-1):
  assert (R+1)%modulus==R+1
  count+=1
print(json.dumps({'remainder_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'P72FirstInputs87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
