from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'FirstMainLargeK.lean').read_text()
for t in ('two_ordinate_impossible X Y eta zeta Delta d','first_ordinate_large (X*Y*Y) tau','hfirst','hmain','8*X*Y*Y+4≤eta+zeta'):assert t in s
for name in ('ordinary14-model-main-square-gap-draft','ordinary14-aux-root-bounds-model-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for m in range(1,14):
 b=2*m-1;delta=(b+1)*(b+3);x,y=1,0
 for n in range(1,8):
  x,y=(b+2)*x+delta*y,x+(b+2)*y
  k=2*y
  assert x*x==1+m*(m+1)*k*k
  if k>2:assert k>=8*m+4
  count+=1
print(json.dumps({'pell_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstMainLargeK.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
