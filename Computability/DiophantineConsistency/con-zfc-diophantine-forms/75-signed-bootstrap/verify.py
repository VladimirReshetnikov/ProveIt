#!/usr/bin/env python3
"""Offline, isolated finite replay. This is not a consistency or kernel proof."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
STAGES=[['check_displayed_system.py'],['guards/build.py'],['guards/check.py'],['guards/review/check_independent.py'],['review/signed34/check_independent.py'],['low_degree/build13.py'],['low_degree/build12.py'],['low_degree/check13.py'],['low_degree/check12.py'],['-O','low_degree/check13.py'],['-O','low_degree/check12.py'],['mixed_source/build.py','21'],['mixed_source/build.py','24'],['mixed_source/build.py','26'],['mixed_source/check.py'],['review/positive/check.py'],['review/positive/check_bindings.py'],['-O','review/positive/check_bindings.py'],['direct/build_initializer.py'],['direct/check_boundary.py'],['certificates/check_certificate.py'],['review/interfaces/check_independent.py'],['review/baseline/count_frontier.py'],['review/baseline/pareto.py']]
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def authenticate(root):
 m=json.loads((root/'SHA256SUMS.json').read_text())
 for name,h in m.items():
  p=root/name;require(p.resolve().is_relative_to(root.resolve()),'Unsafe manifest path');require(p.is_file() and sha(p)==h,'Manifest mismatch: '+name)
 return m
def extract(root):
 pins=json.loads((root/'INCOMING_PINS.json').read_text())
 for a in pins['archives']:
  p=root/'incoming'/a['file'];raw=p.read_bytes();require(len(raw)==a['bytes'] and sha(p)==a['sha256'],'Original archive hash')
  require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==a['git_blob'],'Original archive Git blob')
  dest=root/'sources'/Path(a['file']).stem;dest.mkdir(parents=True,exist_ok=True)
  with zipfile.ZipFile(p) as z:
   require(z.testzip() is None,'Original archive CRC')
   for name in z.namelist():require((dest/name).resolve().is_relative_to(dest.resolve()),'Unsafe ZIP member')
   z.extractall(dest)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--manifest-only',action='store_true');parser.add_argument('--replay-originals',action='store_true',help='Also replay all eight original packages in additional clean copies');args=parser.parse_args()
 require(not sys.flags.optimize,'Run root verifier normally; selected checkers have explicit optimized stages.')
 manifest=authenticate(ROOT)
 if args.manifest_only:print('PASS',len(manifest),'sealed files');return
 rebuild=json.loads((ROOT/'REBUILD_FILES.json').read_text());results=[]
 with tempfile.TemporaryDirectory(prefix='conzfc-wave10-') as td:
  work=Path(td)/'release';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('sources','__pycache__','*.pyc'))
  extract(work);env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONOPTIMIZE',None)
  stages=STAGES+([['review/baseline/replay_inputs.py']] if args.replay_originals else [])
  for stage in stages:
   result=subprocess.run([sys.executable,*stage],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if result.returncode:print(result.stdout);raise RuntimeError('Replay failed: '+' '.join(stage))
   results.append({'stage':stage,'status':'PASS'});print('PASS '+' '.join(stage),flush=True)
  for name in rebuild:require((work/name).read_bytes()==(ROOT/name).read_bytes(),'Nonidentical rebuilt artifact: '+name)
 print(json.dumps({'status':'PASS','stages':results,'stage_count':len(results),'sealed_files':len(manifest),'byte_identical_rebuilt_files':len(rebuild),'original_archives_authenticated_and_extracted':8,'scope':'Finite identities, literal source restoration, metrics, bytes, and diagnostics. Universal mathematical arguments and inherited compiler/calibration dependencies are separate; no new kernel or object-ZFC certificate.'},indent=2))
if __name__=='__main__':main()
