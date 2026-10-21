"""Verify retained production and verbatim upstream receipts; no restore, staging or writes."""
import argparse,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--phase',choices=['before','after'],required=True);a=p.parse_args()
def sha(b):return hashlib.sha256(b).hexdigest()
m=json.loads(a.manifest.read_text());assert len(m['retain'])==27 and len(m['upstream_receipts'])==4
for r in m['retain']+m['upstream_receipts']:
 expected=r['current']if a.phase=='before'or r['action']=='retain_checked_production'else r['upstream'];f=a.repo/r['path']
 index=subprocess.check_output(['git','-C',str(a.repo),'ls-files','--stage','-z','--',r['path']])
 if not expected['present']:
  assert not f.exists()and not f.is_symlink()and not index,r['path'];continue
 assert f.is_file()and not f.is_symlink()and sha(f.read_bytes())==expected['sha256'],r['path']
 mode='100755'if f.stat().st_mode&0o111 else'100644';assert mode==expected['mode'],r['path']
 entries=index.rstrip(b'\0').split(b'\0');assert len(entries)==1
 header,name=entries[0].split(b'\t');imode,oid,stage=header.decode().split()
 assert stage=='0'and name.decode()==r['path']and imode==expected['mode']and oid==expected['blob'],r['path']
 b=subprocess.check_output(['git','-C',str(a.repo),'cat-file','blob',oid]);assert sha(b)==expected['sha256']and len(b)==expected['bytes']
print(json.dumps({'status':'PASS_READ_ONLY_BOUNDARY_CHECK','phase':a.phase,'production':27,'receipts':4,'manifest_sha256':sha(a.manifest.read_bytes()),'checker_sha256':sha(Path(__file__).read_bytes()),'worktree_and_index_checked':True,'git_mutations':False,'proof_tools':False},indent=2))
