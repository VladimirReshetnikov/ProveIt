"""Verify archived source bytes; optional download/extraction, never execute their code.
Usage: python3 verify_archives.py [--download] [--extract]
Requires only Python standard library. Files are written under this script directory.
"""
from pathlib import Path
import argparse,hashlib,json,stat,urllib.parse,urllib.request,zipfile
R=Path(__file__).parent
def require(condition, message):
 if not condition: raise ValueError(message)
p=argparse.ArgumentParser();p.add_argument('--download',action='store_true');p.add_argument('--extract',action='store_true');a=p.parse_args()
c=json.loads((R/'exclusion_catalog.json').read_text())
for s in c['sources']:
 target=R/'downloads'/s['name']
 if a.download and not target.exists():
  ref=s.get('arrival_commit',c['review_pin'])
  url='https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+ref+'/docs/incoming/'+urllib.parse.quote(s['name'])
  with urllib.request.urlopen(url,timeout=120) as u:b=u.read(33*1024*1024)
  require(len(b)<33*1024*1024, 'Download exceeds bound')
 else:b=target.read_bytes()
 require(len(b)==s['size'], 'Size mismatch: '+s['name'])
 require(hashlib.sha256(b).hexdigest()==s['sha256'], 'SHA256 mismatch: '+s['name'])
 require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==s['git_blob'], 'Git blob mismatch: '+s['name'])
 if not target.exists():target.parent.mkdir(exist_ok=True);target.write_bytes(b)
 with zipfile.ZipFile(target) as z:
  require(z.testzip() is None, 'ZIP CRC mismatch')
  if a.extract:
   require(sum(i.file_size for i in z.infolist())<100_000_000, 'ZIP expansion exceeds bound')
   root=R/'extracted'/target.stem
   for i in z.infolist():
    rel=Path(i.filename)
    require(not rel.is_absolute() and '..' not in rel.parts and '\\' not in i.filename, 'Unsafe ZIP path')
    require(not stat.S_ISLNK(i.external_attr>>16), 'ZIP symlink rejected')
    f=root/rel
    if i.is_dir():f.mkdir(parents=True,exist_ok=True)
    else:f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(z.read(i))
 print('Verified',s['id'],s['name'])
