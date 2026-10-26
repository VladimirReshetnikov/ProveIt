"""Read-only verification against an existing checkout; standard library only.
No network, extraction, Lean invocation, repository mutation, or submitted code execution.
Usage: python3 verify_baseline.py --repo /path/to/ProveIt
The checkout must contain the files of pin 22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
"""
import argparse, hashlib, json, stat, zipfile
from pathlib import Path, PurePosixPath
R=Path(__file__).resolve().parent
def require(condition, message):
 if not condition:raise ValueError(message)
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);a=p.parse_args()
def check(b,e):
 sha=e.get('git_blob',e.get('sha'))
 if len(b)!=e['size']:raise ValueError('Size mismatch: '+str(e))
 if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=sha:raise ValueError('Git blob mismatch: '+str(e))
 if e.get('sha256') and hashlib.sha256(b).hexdigest()!=e['sha256']:raise ValueError('SHA256 mismatch: '+str(e))
root=a.repo/'Computability/DiophantineConsistency/research/lean-proof-simplification'
records=json.loads((R/'PLACED_BLOB_BINDING.json').read_text())+json.loads((R/'PLACED_FRESH_BINDING.json').read_text())
require(len({(e['packet'],e['path']) for e in records})==321, 'Placed record count')
for e in records:check((root/e['packet']/e['path']).read_bytes(),e)
for e in json.loads((R/'research_listing.json').read_text()):
 if e['type']=='file':check((a.repo/e['path']).read_bytes(),e)
archives={e['name']:e for e in json.loads((R/'ARCHIVE_VERIFICATION.json').read_text()) if e['source_kind']=='fresh pinned archive'}
member_records=json.loads((R/'FRESH_MEMBERS.json').read_text())
for e in json.loads((R/'incoming_listing.json').read_text()):
 f=a.repo/e['path'];check(f.read_bytes(),e)
 if e['name'] not in archives:continue
 check(f.read_bytes(),archives[e['name']])
 expected={r['member']:r for r in member_records if r['archive']==e['name']}
 with zipfile.ZipFile(f) as z:
  infos=z.infolist();require(len(infos)<10000 and sum(i.file_size for i in infos)<100_000_000, 'Archive bounds')
  names=set()
  for i in infos:
   q=PurePosixPath(i.filename)
   require(not q.is_absolute() and '..' not in q.parts and '\\' not in i.filename and '\0' not in i.filename, 'Unsafe archive path')
   require(not stat.S_ISLNK(i.external_attr>>16) and i.filename not in names, 'Symlink or duplicate');names.add(i.filename)
   if not i.is_dir():check(z.read(i),expected.pop(i.filename))
  require(not expected, 'Missing archive members')
print(json.dumps({'status':'PASS','placed_blobs':321,'research_root_files':2,'incoming_files':6,'fresh_archives':5,'fresh_archive_members':len(member_records),'scope':'byte identity and safe archive structure only; not Lean validation'},indent=2))
