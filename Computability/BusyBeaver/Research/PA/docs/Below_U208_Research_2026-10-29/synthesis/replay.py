from pathlib import Path
import tempfile,shutil,json,hashlib,subprocess,sys
P=Path(__file__).resolve().parent

def check(condition,message):
 if not condition:raise RuntimeError(message)
manifest=json.loads((P/'MANIFEST.json').read_text())
actual={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest()for p in P.rglob('*')if p.is_file() and p.name!='MANIFEST.json' and '__pycache__'not in p.parts}
check(actual==manifest,'sealed content mismatch')
full='--full'in sys.argv
jobs=[('conditional_pair.py',['conditional_results.json']),('macro_pair.py',['macro_results.json']),('offset.py',['offset_results.json']),('offset_initial.py',['initial_offset_results.json'])]
if full:jobs.append(('offset_neutral.py',['primary_offset_neutral_results.json','compatibility_offset_neutral_results.json']))
with tempfile.TemporaryDirectory(prefix='u208-synthesis-')as tmp:
 w=Path(tmp)/'work';shutil.copytree(P,w)
 for script,outputs in jobs:
  p=subprocess.run([sys.executable,'-B',str(w/script)],cwd=w,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  check(p.returncode==0,script+' failed: '+p.stdout[-4000:])
  for output in outputs:
   got=json.loads((w/output).read_text());want=json.loads((w/'receipts'/output).read_text())
   if isinstance(got,dict):got.pop('neutral_receipt',None);want.pop('neutral_receipt',None)
   check(got==want,output+' changed')
  print('PASS',script,flush=True)
print('PASS sealed',len(manifest),'files; full=',full)
