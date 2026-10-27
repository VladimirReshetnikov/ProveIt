"""Replay original certificate checks with optimization and negative controls."""
import hashlib,json,subprocess,sys,tempfile
from pathlib import Path
P=Path(__file__).resolve().parent
records=[]
for name in ['check_certificate.py','check_lowdegree.py']:
 payload=[]
 for opt in [[],['-O']]:
  r=subprocess.run([sys.executable,*opt,str(P/name)],capture_output=True,text=True)
  if r.returncode:raise RuntimeError(f'{name} {opt} failed: {r.stderr}')
  payload.append(r.stdout)
  records.append({'name':name,'mode':'optimized' if opt else 'normal','returncode':r.returncode,'stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest()})
 if payload[0]!=payload[1]:raise RuntimeError(f'{name} changed under -O')
 negative=(P/name).read_text()
 old,new=('root_hi<38','root_hi<37') if name=='check_certificate.py' else ('Thi<F(143,10)','Thi<F(140,10)')
 if old not in negative:raise RuntimeError('negative-control target missing')
 negative=negative.replace(old,new,1)
 with tempfile.TemporaryDirectory() as d:
  f=Path(d)/name;f.write_text(negative)
  for opt in [[],['-O']]:
   r=subprocess.run([sys.executable,*opt,str(f)],capture_output=True,text=True)
   if r.returncode==0 or 'RuntimeError' not in r.stderr:raise RuntimeError('negative control did not fail explicitly')
   records.append({'name':name,'mode':'negative_optimized' if opt else 'negative_normal','returncode':r.returncode,'expected_explicit_failure':True})
(P/'verification_runs.json').write_text(json.dumps({'status':'PASS','runs':records},indent=2)+'\n')
print(json.dumps({'status':'PASS','runs':records},indent=2))
