from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentTo88First.lean').read_text()
for t in ('RingParentTo88Draft.first_eval','ParentTo88FirstCutDraft.fresh_first_cut','P72Root.cast_port p 0','hY :','htau :','theorem first_zero'):assert t in s
for name in ('ordinary13-parent-to-88-ring-client-draft','ordinary14-parent-to-88-first-cut-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for q in range(1,8):
 for b in range(1,7):
  for Yq in range(1,5):
   for tau in range(1,10):
    Q=q**3;Y=Q*Yq;M=Q*b;ell=9;k=3;sigma=ell+k+Yq+tau
    assert M*(ell+k-sigma)+Y*b==-M*tau
    count+=1
print(json.dumps({'first_cut_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentTo88First.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
