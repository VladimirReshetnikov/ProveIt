#!/usr/bin/env python3
"""Offline exact replay in independent disposable copies. Standard library only.
The checks verify finite objects, not consistency or a new formal calibration.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
EXEMPT={'MANIFEST_SHA256.json','REPLAY.json','ISOLATED_REPLAY.json'}
def require(ok,message):
 if not ok:raise ValueError(message)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
 files={p.relative_to(ROOT).as_posix():p for p in ROOT.rglob('*') if p.is_file()}
 require(not any(p.is_symlink() for p in ROOT.rglob('*')),'Symlinks are not accepted')
 manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
 mf=manifest['files'];require(set(files)-EXEMPT==set(mf),'Exact manifest inventory mismatch: '+str(sorted((set(files)-EXEMPT)^set(mf))))
 for name,row in mf.items():
  p=Path(name);require(not p.is_absolute() and '..' not in p.parts,'Unsafe manifest path')
  require(files[name].stat().st_size==row['bytes'] and digest(files[name])==row['sha256'],'Manifest mismatch '+name)
 return mf

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);ap.add_argument('--mode',choices=['both','normal','optimized'],default='both');a=ap.parse_args()
 begin=time.monotonic();mf=inventory();plan=json.loads((ROOT/'VERIFY_PLAN.json').read_text())
 modes=[False,True] if a.mode=='both' else [a.mode=='optimized']
 result={'status':'RUNNING','mode':a.mode,'manifest_files':len(mf),'scope':'Exact finite algebra, authentic numerical ports, byte-identical reconstruction and corruption controls; ordinary unbounded semantics and inherited logical calibration remain separate.','commands':[],'byte_equalities':[]}
 with tempfile.TemporaryDirectory(prefix='conzfc_round17_') as td:
  temp=Path(td)
  # Each mode starts from the same immutable reference. Preserve any caller's
  # PYTHONPATH audit hook; neither imports nor subprocesses may evade isolation.
  env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
  for optimized in modes:
   mode='optimized' if optimized else 'normal';work=temp/mode;shutil.copytree(ROOT,work)
   output=temp/(mode+'-outputs');output.mkdir()
   for item in plan['commands']:
    command=[sys.executable,'-B']+(['-O'] if optimized else [])
    command += [s.replace('{output}',str(output)).replace('{root}',str(work)).replace('{mode}',mode) for s in item['args']]
    start=time.monotonic();p=subprocess.run(command,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    require(p.returncode==0,item['name']+' failed:\n'+p.stdout[-30000:])
    result['commands'].append({'name':item['name'],'optimized':optimized,'seconds':round(time.monotonic()-start,3),'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest()})
    print('PASS '+item['name']+(' [-O]' if optimized else ''),flush=True)
   for name in plan['byte_compare']:
    expected=ROOT/name;actual=work/name
    require(actual.is_file() and actual.read_bytes()==expected.read_bytes(),'Rebuild byte mismatch '+name)
    result['byte_equalities'].append({'file':name,'mode':mode,'sha256':digest(actual),'bytes':actual.stat().st_size})
  inventory() # The references were never changed by a mutating checker.
 result.update(status='PASS',isolated_temporary_copies=True,reference_unchanged=True,commands_passed=len(result['commands']),byte_equalities_passed=len(result['byte_equalities']),elapsed_seconds=round(time.monotonic()-begin,3))
 text=json.dumps(result,indent=2)+'\n'
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(text)
 print(text)
if __name__=='__main__':main()
