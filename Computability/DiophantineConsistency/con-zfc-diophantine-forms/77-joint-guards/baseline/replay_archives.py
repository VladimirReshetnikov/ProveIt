from pathlib import Path
import json,hashlib,os,sys,subprocess,tempfile,shutil,concurrent.futures,time
R=Path(__file__).resolve().parents[1];O=Path(__file__).resolve().parent
P=json.loads((R/'INCOMING_PINS.json').read_text())
def hashes(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
def run(v):
 a,mode=v;root=next(p for p in (R/'sources'/Path(a['file']).stem).iterdir() if p.is_dir());before=hashes(root)
 script='verify.py' if (root/'verify.py').exists() else 'verify_all.py';args=[sys.executable,'-B']
 if mode=='optimized':
  if 'residue-orientation' in a['file']:args += [script,'--optimized']
  else:args += ['-O',script]
 else:args += [script]
 with tempfile.TemporaryDirectory(prefix='wave11-input-') as td:
  w=Path(td)/'release';shutil.copytree(root,w,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));start=time.monotonic();env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
  p=subprocess.run(args,cwd=w,env=env,capture_output=True,text=True,timeout=1200)
  tag=Path(a['file']).stem+'.'+mode;(O/(tag+'.stdout.txt')).write_text(p.stdout);(O/(tag+'.stderr.txt')).write_text(p.stderr)
  changed=[n for n,h in before.items() if (w/n).is_file() and hashlib.sha256((w/n).read_bytes()).hexdigest()!=h]
  result={'archive':a['file'],'command':args,'mode':mode,'returncode':p.returncode,'status':'PASS' if p.returncode==0 else 'FAIL','seconds':round(time.monotonic()-start,3),'original_unchanged':before==hashes(root),'changed_existing_in_copy':changed,'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr.encode()).hexdigest()}
  print(json.dumps(result),flush=True);return result
jobs=[(a,'normal') for a in P['archives']]+[(a,'optimized') for a in P['archives'] if 'Signed_Bootstrap' not in a['file']]
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as e:out=list(e.map(run,jobs))
(O/'REPLAY_RESULTS.json').write_text(json.dumps({'status':'PASS' if all(x['status']=='PASS' and x['original_unchanged'] for x in out) else 'FAIL','runs':out,'scope':'Original archives, clean-copy finite arithmetic/data replay following source inspection. No Lean build or universal proof claim; signed-bootstrap root has selected optimized phases but forbids optimized root.'},indent=2)+'\n')
if not all(x['status']=='PASS' and x['original_unchanged'] for x in out):
 raise RuntimeError('An original archive replay failed or altered its authenticated input tree')
print('PASS all',len(out),'original archive root phases')
