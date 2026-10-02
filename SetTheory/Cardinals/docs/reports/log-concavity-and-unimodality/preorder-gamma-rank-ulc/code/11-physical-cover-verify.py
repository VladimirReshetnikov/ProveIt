#!/usr/bin/env python3
"""Read-only nested dependency and new assembly replay; standard library only."""
from pathlib import Path,PurePosixPath
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile,time,zipfile

ROOT=Path(__file__).resolve().parent
DEPENDENCY_SHA='718fcbed392be1520ad2fe09313ff18b10b38a5338f5a704cbad2cf7b7b8c488'
JOBS=[
 ('producer-assembly','reproducibility/producer/check_internal_assembly.py','assembly_verification.json'),
 ('independent-assembly','reproducibility/independent/check_assembly.py','independent_receipt.json'),
]

def canonical(v):
 if isinstance(v,dict):return{k:canonical(x)for k,x in v.items()if k not in {'seconds','elapsed_seconds'}}
 if isinstance(v,list):return[canonical(x)for x in v]
 return v

def run(script,directory):
 result=subprocess.run([sys.executable,str(script)],cwd=directory,
  env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),text=True,capture_output=True)
 if result.returncode:
  print(result.stdout);print(result.stderr,file=sys.stderr)
  raise AssertionError(f'Failed replay: {script.name}')
 return result.stdout

def main():
 start=time.monotonic();count=0
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,relative=line.split('  ',1);p=ROOT/relative
  assert p.is_file(),f'Missing release file: {relative}'
  assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'Hash mismatch: {relative}'
  count+=1
 print(f'PASS: {count} release file hashes',flush=True)
 dep=ROOT/'dependency/three-core-rayleigh-result.zip'
 assert hashlib.sha256(dep.read_bytes()).hexdigest()==DEPENDENCY_SHA
 results=[]
 with tempfile.TemporaryDirectory(prefix='physical-cover-three-replay-')as tmp:
  base=Path(tmp);target=base/'dependency';target.mkdir()
  with zipfile.ZipFile(dep)as archive:
   names=archive.namelist();assert len(names)==len(set(names))
   assert archive.testzip()is None
   for info in archive.infolist():
    p=PurePosixPath(info.filename)
    assert not p.is_absolute() and '..'not in p.parts
    assert not stat.S_ISLNK(info.external_attr>>16)
   archive.extractall(target)
  directory=target/'three-core-rayleigh-result'
  print(run(directory/'verify.py',directory),end='')
  print('PASS: complete frozen boundary dependency replay',flush=True)
  results.append({'checker':'frozen-boundary-dependency','verdict':'PASS'})
  for name,relative,output in JOBS:
   source=ROOT/relative;directory=base/name;directory.mkdir()
   copied=directory/source.name;shutil.copyfile(source,copied)
   run(copied,directory)
   actual=json.loads((directory/output).read_text())
   expected=json.loads(source.with_name(output).read_text())
   assert canonical(actual)==canonical(expected),f'Receipt mismatch: {name}'
   print(f'PASS: {name}; all deterministic receipt fields match',flush=True)
   results.append({'checker':name,'verdict':'PASS'})
 print(json.dumps({'verdict':'PASS','manifest_files':count,'checks':results,
  'elapsed_seconds':round(time.monotonic()-start,3)},indent=2))

if __name__=='__main__':main()
