from pathlib import Path
import hashlib,json,subprocess,tempfile,sys,os
P=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def hashes():return{str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest()for f in P.rglob('*')if f.is_file()and f.name!='MANIFEST.json'and '__pycache__'not in f.parts}
before=hashes();need(before==json.loads((P/'MANIFEST.json').read_text()),'integrity');checks=[]
with tempfile.TemporaryDirectory(prefix='reachability-')as t:
 out=Path(t)/'certificate.json';env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'};env.pop('PYTHONOPTIMIZE',None)
 def run(label,args):
  r=subprocess.run([sys.executable,'-B',*map(str,args)],env=env,capture_output=True,text=True);need(r.returncode==0,label+'\n'+r.stdout+'\n'+r.stderr);checks.append(label)
 run('generate',[P/'generate.py',P/'inputs/compatibility.sites.json',out]);need(json.loads(out.read_text())==json.loads((P/'certificate.json').read_text()),'deterministic certificate')
 for opts,label in[([], 'normal'),(['-O'],'optimized')]:
  run('independent invariant '+label,[*opts,P/'check.py',P/'inputs/compatibility.sites.json',out,'--other',P/'inputs/joint.sites.json'])
  run('five corruption controls '+label,[*opts,P/'negative.py'])
need(hashes()==before,'changed');print(json.dumps({'status':'PASS','checks':checks,'sealed_files':len(before)},indent=2))
