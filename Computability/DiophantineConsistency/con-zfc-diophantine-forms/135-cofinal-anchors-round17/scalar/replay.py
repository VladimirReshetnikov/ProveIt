#!/usr/bin/env python3
"""Authenticate, reconstruct and check the portable scalar release in isolation."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 manifest=json.loads((ROOT/'RELEASE_WHITELIST.json').read_text())
 require(manifest['schema']=='portable-scalar-release-v1','manifest schema')
 for name,record in manifest['files'].items():
  p=Path(name);require(not p.is_absolute() and '..' not in p.parts,'relative safe path')
  raw=(ROOT/p).read_bytes();require(len(raw)==record['bytes'] and digest(raw)==record['sha256'],'pinned release file '+name)
 with tempfile.TemporaryDirectory(prefix='cofactor11-replay-') as td:
  dest=Path(td)
  for name in manifest['files']:
   target=dest/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,target)
  env=dict(os.environ);env.pop('PYTHONPATH',None);env['PYTHONDONTWRITEBYTECODE']='1'
  runs=[]
  for command in [['build.py'],['check.py'],['-O','check.py']]:
   run=subprocess.run([sys.executable,'-B']+command,cwd=dest,env=env,text=True,capture_output=True)
   require(run.returncode==0,'clean replay failed '+repr(command)+'\n'+run.stderr)
   runs.append({'command':['python']+command,'returncode':run.returncode,'stdout_sha256':digest(run.stdout.encode())})
  generated=['METRICS.json','CHECK.json','CHECK_OPTIMIZED.json']+[p.name for p in ROOT.glob('*cofactor11_*.json')]
  for name in generated:require((ROOT/name).read_bytes()==(dest/name).read_bytes(),'rebuild differs '+name)
  result={'status':'PASS','isolated_temporary_directory':True,'producer_output_byte_identical':True,'normal_and_optimized_checker_pass':True,'all_live_gate_degree_certificates_rebuilt':True,'complete_six_port_payload_and_recipe_rebuilt':True,'pinned_release_files':len(manifest['files']),'generated_files_compared':generated,'runs':runs}
 (ROOT/'REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
