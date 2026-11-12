from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'FirstRootGap88.lean').read_text()
for t in ('FirstQuotient88Draft.quotient_and_root','MainNorm88Draft.main_norm','FirstMainLargeKDraft.first_main_large_k','FirstRootGapDraft.root_gt_linear','have hsm : s≤m','P88QuotientGuarded.graph p'):assert t in s
for name in ('ordinary14-88-first-quotient-draft','ordinary14-88-main-norm-draft','ordinary14-first-main-large-k-draft','ordinary14-first-root-gap-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for X in range(1,9):
 for q in range(1,8):
  for s0 in range(1,8):
   Y=q**3*s0;m=X*Y*Y
   assert s0<=m
   count+=1
print(json.dumps({'quotient_size_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstRootGap88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
