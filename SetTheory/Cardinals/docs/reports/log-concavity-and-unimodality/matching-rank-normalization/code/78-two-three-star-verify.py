#!/usr/bin/env python3
"""Read-only certificate and frozen-dependency replay."""
if not __debug__:raise SystemExit('Run without -O; assertions are required.')
from pathlib import Path,PurePosixPath
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile,time,zipfile
ROOT=Path(__file__).resolve().parent
DEP_SHA='1d054c58ce0f18a1418b086a3b4663cc1fdf0b5ecc191ec515e9239f545e1aff'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(v):
 if isinstance(v,dict):return{k:canonical(x)for k,x in v.items()if k not in {'seconds','elapsed_seconds'}}
 if isinstance(v,list):return[canonical(x)for x in v]
 return v
def manifest(root):
 found={}
 for line in (root/'SHA256SUMS').read_text().splitlines():
  sha,name=line.split('  ',1);assert name not in found and digest(root/name)==sha,name;found[name]=sha
 actual={p.relative_to(root).as_posix()for p in root.rglob('*')if p.is_file()and p.name!='SHA256SUMS'}
 assert actual==set(found),'Manifest coverage is not exact'
 return found
def run(script,cwd,args=()):
 result=subprocess.run([sys.executable,str(script),*map(str,args)],cwd=cwd,text=True,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 if result.returncode:
  print(result.stdout);print(result.stderr,file=sys.stderr);raise AssertionError(script.name)
 return result.stdout
def compare(actual,expected,label):
 assert canonical(actual)==canonical(expected),f'Receipt mismatch: {label}'
 print(f'PASS: {label}; every deterministic receipt field matches',flush=True)
def main():
 start=time.monotonic();initial=manifest(ROOT);results=[]
 print(f'PASS: {len(initial)} release hashes and exact manifest coverage',flush=True)
 dep=ROOT/'dependency/complete-two-by-three-result.zip';assert digest(dep)==DEP_SHA
 with tempfile.TemporaryDirectory(prefix='all-two-by-three-replay-')as temp:
  base=Path(temp);directory=base/'dependency';directory.mkdir()
  with zipfile.ZipFile(dep)as archive:
   names=archive.namelist();assert len(names)==len(set(names));assert archive.testzip()is None
   for info in archive.infolist():
    p=PurePosixPath(info.filename);assert not p.is_absolute()and '..'not in p.parts
    assert not stat.S_ISLNK(info.external_attr>>16)
   archive.extractall(directory)
  nested=directory/'complete-two-by-three-result'
  print(run(nested/'verify.py',nested),end='')
  assert (ROOT/'dependency/complete-two-by-three.pdf').read_bytes()==(nested/'article/complete-two-by-three.pdf').read_bytes()
  assert (ROOT/'dependency/matching-rank-four.pdf').read_bytes()==(nested/'dependency/matching-rank-four.pdf').read_bytes()
  results.append('complete frozen complete-core and rank-four dependency replay')
  data=base/'data';data.mkdir()
  for source in [*(ROOT/'certificates').glob('*.json'),*(ROOT/'proof-notes').glob('*.md')]:shutil.copyfile(source,data/source.name)
  producer=ROOT/'reproducibility/producer/replay_core_certificates.py';copied=data/producer.name;shutil.copyfile(producer,copied)
  run(copied,data);actual=json.loads((data/'core_exact_replay.json').read_text())
  compare(actual,json.loads(producer.with_name('core_exact_replay.json').read_text()),'producer exact middle certificates');results.append('producer middle certificates')
  producer_records=actual['records']
  for folder,flag,source_dir in [('independent-middles','--data-dir',data),('independent-stars','--source-dir',ROOT/'proof-notes')]:
   target=base/folder;target.mkdir();source=ROOT/'reproducibility'/folder/'check.py';copied=target/'check.py';shutil.copyfile(source,copied)
   run(copied,target,[flag,source_dir,'--output-dir',target]);actual=json.loads((target/'independent_receipt.json').read_text())
   compare(actual,json.loads(source.with_name('independent_receipt.json').read_text()),folder);results.append(folder)
   if folder=='independent-middles':
    mine={(r['mask'],r['gap']):(r['target_sha256'],r['remainder_sha256'])for r in producer_records}
    theirs={(r['mask'],r['gap']):(r['target_sha256'],r['remainder_sha256'])for r in actual['records']}
    assert mine==theirs and len(mine)==26
  print('PASS: all 26 independent target and remainder hashes agree',flush=True)
 assert manifest(ROOT)==initial
 print(json.dumps({'verdict':'PASS','manifest_files':len(initial),'checks':results,'middle_target_remainder_hashes_agree':True,'elapsed_seconds':round(time.monotonic()-start,3)},indent=2))
if __name__=='__main__':main()
