#!/usr/bin/env python3
"""Portable fresh exact replay. Python standard library only."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tarfile,tempfile,time
ROOT=Path(__file__).resolve().parent
BRANCHES=[('four-active',('four-active-certificates.tar.xz',),'four-active-cubic','four_active_cores.txt',3044,166857515),('four-sink',('four-sink-certificates-a.tar.xz','four-sink-certificates-b.tar.xz'),'four-sink-moment-cubic','cores.txt',9608,1536514154)]

def integrity():
 count=0
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,name=line.split('  ',1);p=ROOT/name
  if not p.is_file():raise RuntimeError('Missing file: '+name+'. Extract both delivery ZIPs into the same parent folder before full replay.')
  if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:raise RuntimeError('Hash mismatch: '+name)
  count+=1
 return count

def unpack_branch(source,branch):
 family,archives,directory,catalog,count,total=branch
 records=json.loads((ROOT/'audits'/f'{family}-certificate-manifest.json').read_text())
 expected={f'{directory}/certificate_{r["id"]}.json':r['certificate_sha256']for r in records}
 assert set(expected)=={f'{directory}/certificate_{i}.json'for i in range(count)}
 seen=set();expanded=0;(source/directory).mkdir()
 # Stream files individually; never use unrestricted tar extraction.
 for archive in archives:
  with tarfile.open(ROOT/archive,'r|xz')as tar:
   for member in tar:
    if not member.isfile()or member.name not in expected or member.name in seen:raise RuntimeError('Unexpected archive member: '+member.name)
    if member.size<0 or expanded+member.size>total:raise RuntimeError('Unexpected uncompressed size')
    reader=tar.extractfile(member)
    if reader is None:raise RuntimeError('Archive member has no file data')
    digest=hashlib.sha256();written=0;target=source/member.name
    with target.open('xb')as out:
     while True:
      block=reader.read(1024*1024)
      if not block:break
      out.write(block);digest.update(block);written+=len(block)
    assert written==member.size
    if digest.hexdigest()!=expected[member.name]:raise RuntimeError('Decoded certificate hash mismatch: '+member.name)
    expanded+=written;seen.add(member.name)
 assert seen==set(expected) and expanded==total
 shutil.copyfile(ROOT/'catalogs'/catalog,source/catalog)
 return {'family':family,'files':count,'bytes':expanded,'decoded_certificate_hashes_match_independent_manifest':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['full','hashes'],default='full');ap.add_argument('--workers',type=int,default=4);ap.add_argument('--output');a=ap.parse_args()
 if a.workers<1:ap.error('--workers must be positive')
 start=time.time();result={'pass':True,'mode':a.mode,'integrity_entries':integrity()}
 if a.mode=='full':
  with tempfile.TemporaryDirectory(prefix='five-core-boundary-proof-')as tmp:
   tmp=Path(tmp);source=tmp/'certificate-data';source.mkdir();checker=tmp/'check.py';shutil.copyfile(ROOT/'proof-check/check.py',checker);result['decoded_data']=[];result['certificate_replays']=[]
   for branch in BRANCHES:
    print('Unpacking byte-identical proof data:',branch[0],flush=True)
    result['decoded_data'].append(unpack_branch(source,branch));receipt=tmp/(branch[0]+'-fresh-receipt.json')
    subprocess.run([sys.executable,str(checker),branch[0],str(source),str(receipt),str(a.workers)],check=True)
    result['certificate_replays'].append(json.loads(receipt.read_text()))
   ordinary=tmp/'check_ordinary_lemmas.py';shutil.copyfile(ROOT/'proof-check/check_ordinary_lemmas.py',ordinary)
   subprocess.run([sys.executable,str(ordinary)],check=True)
   result['ordinary_corroboration']=json.loads((tmp/'verification-receipt.json').read_text())
 result['elapsed_seconds']=round(time.time()-start,3)
 if a.output:Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
