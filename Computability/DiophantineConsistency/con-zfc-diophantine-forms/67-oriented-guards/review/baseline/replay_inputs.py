from pathlib import Path
import json,hashlib,os,sys,subprocess,tempfile,shutil,concurrent.futures,time
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent
P=json.loads((R/'INCOMING_PINS.json').read_text());scripts=['verify_all.py','verify_all.py','reproduce.py','verify.py','verify_release.py','verify.py']
def hashes(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and '__pycache__'not in f.parts}
def run(v):
 a,script=v;root=next(p for p in (R/'sources'/Path(a['file']).stem).iterdir() if p.is_dir());before=hashes(root)
 with tempfile.TemporaryDirectory(prefix='wave9-input-') as td:
  w=Path(td)/'release';shutil.copytree(root,w,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));start=time.monotonic();env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
  p=subprocess.run([sys.executable,'-B',script],cwd=w,env=env,capture_output=True,text=True,timeout=1200)
  tag=Path(a['file']).stem;(O/(tag+'.stdout.txt')).write_text(p.stdout);(O/(tag+'.stderr.txt')).write_text(p.stderr)
  changed=[n for n,h in before.items() if (w/n).is_file() and hashlib.sha256((w/n).read_bytes()).hexdigest()!=h]
  result={'archive':a['file'],'script':script,'returncode':p.returncode,'status':'PASS' if p.returncode==0 else 'FAIL','seconds':round(time.monotonic()-start,3),'original_unchanged':before==hashes(root),'changed_existing_in_copy':changed,'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr.encode()).hexdigest()}
  print(json.dumps(result),flush=True);return result
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as e:out=list(e.map(run,zip(P['archives'],scripts)))
(O/'REPLAY_RESULTS.json').write_text(json.dumps({'status':'PASS' if all(x['status']=='PASS' and x['original_unchanged'] for x in out) else 'FAIL','runs':out,'scope':'Finite original release replays, after read-only program review; no Lean rebuild or universal proof claim.'},indent=2)+'\n')
