"""Recover only pinned inert inputs. Never import, compile or execute fetched code.
Usage: python3 -B code/fetch_inputs.py [--archive-dir DIR] [--output PACKAGE]
DIR must contain source245.zip with the exact INPUTS.json archive identity.
Without DIR, pinned public raw GitHub archive URLs are read into memory.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,urllib.request,zipfile,sys
ROOT=Path(__file__).resolve().parent.parent
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
def require(ok,why):
 if not ok:raise ValueError(why)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--archive-dir',type=Path);ap.add_argument('--output',type=Path,default=ROOT);a=ap.parse_args();root=a.output.resolve();m=json.loads((ROOT/'INPUTS.json').read_text());pending=[]
 for key,c in m['archives'].items():
  if a.archive_dir:raw=(a.archive_dir/c['local_basename']).read_bytes()
  else:
   req=urllib.request.Request(c['url'],headers={'User-Agent':'ProveIt-continuation-data-recovery/1'})
   with urllib.request.urlopen(req,timeout=120)as r:raw=r.read(c['bytes']+1)
  require(len(raw)==c['bytes']and digest(raw)==c['sha256'],'Archive size/hash mismatch: '+key)
  require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==c['git_blob_sha1'],'Archive Git identity mismatch: '+key)
  with zipfile.ZipFile(io.BytesIO(raw))as z:
   names=z.namelist();require(len(names)==len(set(names)),'Duplicate archive names')
   for x in c['members']:
    member=PurePosixPath(x['member']);dest=PurePosixPath(x['destination'])
    require(not member.is_absolute()and'..'not in member.parts,'Unsafe member')
    require(not dest.is_absolute()and'..'not in dest.parts,'Unsafe destination')
    info=z.getinfo(str(member));require(not info.is_dir()and not stat.S_ISLNK(info.external_attr>>16),'Non-regular input')
    require(info.file_size==x['bytes'],'Member size mismatch');content=z.read(info);require(digest(content)==x['sha256'],'Member hash mismatch: '+str(member))
    target=(root/str(dest)).resolve();require(target.is_relative_to(root),'Destination escapes root')
    require(not target.exists()or digest(target.read_bytes())==x['sha256'],'Refusing to replace different existing input: '+str(dest))
    pending.append((target,content))
 # Validate every archive and member before writing any input.
 for path,content in pending:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(content)
 print(f'PASS: {len(pending)} pinned inert input destinations recovered; no downloaded code executed')
if __name__=='__main__':main()
