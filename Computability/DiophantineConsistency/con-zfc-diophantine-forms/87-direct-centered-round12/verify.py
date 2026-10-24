#!/usr/bin/env python3
"""Authenticate and replay only the explicit authored-code allowlist in isolation."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
R=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--quick',action='store_true',help='normal mode only; default also repeats all checks under -O');p.add_argument('--output',type=Path);a=p.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(v,msg):
 if not v:raise ValueError(msg)
manifest=json.loads((R/'MANIFEST.json').read_text());files=manifest['files']
for name,row in files.items():
 f=R/name;req(f.is_file(),'missing '+name);req(f.stat().st_size==row['bytes'] and sha(f)==row['sha256'],'manifest mismatch '+name)
plan=json.loads((R/'REPLAY.json').read_text());receipts=[]
with tempfile.TemporaryDirectory(prefix='con-zfc-r12-replay-') as td:
 T=Path(td)/'packet';shutil.copytree(R,T,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
 modes=[False] if a.quick else [False,True]
 for optimized in modes:
  for row in plan['commands']:
   argv=[sys.executable]+(['-O'] if optimized else [])+row['args'];cwd=T/row.get('cwd','.')
   start=time.monotonic();r=subprocess.run(argv,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=row.get('timeout',600))
   req(r.returncode==0,'failed '+str(argv)+'\n'+r.stdout[-12000:])
   receipts.append({'args':row['args'],'cwd':row.get('cwd','.'),'optimized':optimized,'seconds':round(time.monotonic()-start,3),'output_sha256':hashlib.sha256(r.stdout.encode()).hexdigest()})
   print(('optimized ' if optimized else 'normal ')+str(row['args'])+' PASS',flush=True)
  for name,expected in plan['literal_sha256'].items():req(sha(T/name)==expected,'regeneration mismatch '+name)
result={'status':'PASS','scope':'manifest authentication; isolated authored-code allowlist; byte-exact literal regeneration; normal/optimized modes; mutation rejection','manifest_files':len(files),'modes':['normal'] if a.quick else ['normal','optimized'],'literal_files_checked':len(plan['literal_sha256']),'commands':receipts}
if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
