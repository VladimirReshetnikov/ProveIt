from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentFirst88.lean').read_text()
for t in ('Guard88Draft.bt_of_zero','Ring88ToParentDraft.first_cut','Ring88ToParentDraft.first_eval','hrel :','htau :','P88FourSquare.graph p'):assert t in s
for name in ('ordinary14-88-guard-draft','ordinary14-88-parent-ring-client-draft','ordinary14-88-first-quotient-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q3 in range(1,7):
 for b in range(1,6):
  for t in range(1,6):
   for ell in range(5):
    for k in range(1,5):
     s0=1;tau=ell+s0+1;r=k*b*t+t+tau-ell-k-s0
     Z=q3*b*(ell+k+r-k*b*t)+q3*s0*b-q3*b*t
     assert Z==q3*b*tau
     count+=1
print(json.dumps({'fresh_first_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentFirst88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
