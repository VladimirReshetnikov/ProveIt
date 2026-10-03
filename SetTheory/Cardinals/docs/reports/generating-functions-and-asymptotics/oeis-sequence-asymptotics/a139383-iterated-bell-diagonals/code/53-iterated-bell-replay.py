"""Offline clean replay. Generated files live in a fresh temporary directory."""
import json,subprocess,sys,tempfile,time,hashlib
from pathlib import Path
base=Path(__file__).resolve().parents[1]
manifest=base/'manifest.json'
if manifest.exists():
 data=json.loads(manifest.read_text())
 for item in data['files']:
  rel=Path(item['path']);assert not rel.is_absolute() and '..' not in rel.parts
  path=base/rel;assert path.is_file() and not path.is_symlink()
  assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],str(rel)
 print('MANIFEST PASS',len(data['files']))
results=[]
with tempfile.TemporaryDirectory(prefix='iterated-bell-replay-') as d:
 for name,args in [
 ('exact_recurrence',['check_recurrence.py','--max','260','--out',str(Path(d)/'recurrence.json')]),
 ('coefficient_and_remainder_generator',['generate_coefficients.py','--order','3','--out',str(Path(d)/'coefficients.json')]),
 ('outward_interval_amplitude',['verify_amplitude.py'])]:
  start=time.monotonic();cmd=[sys.executable,str(base/'verification'/args[0]),*args[1:]]
  run=subprocess.run(cmd,cwd=base,text=True,capture_output=True)
  print(f'--- {name} ---');print(run.stdout)
  if run.returncode:print(run.stderr,file=sys.stderr);raise SystemExit(run.returncode)
  results.append({'check':name,'passed':True,'seconds':round(time.monotonic()-start,3)})
print(json.dumps({'all_passed':True,'checks':results},indent=2))
