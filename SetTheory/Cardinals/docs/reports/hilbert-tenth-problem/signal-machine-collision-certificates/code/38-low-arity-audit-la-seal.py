#!/usr/bin/env python3
"""Seal only this newly authored audit directory and a new neighboring archive."""
import hashlib,json,os,stat,zipfile
from pathlib import Path
root=Path(__file__).resolve().parent
assert root.name=='independent-low-arity-audit-20261004'
archive=root.with_suffix('.zip');receipt=root.parent/(root.name+'-receipt.json')
assert not archive.exists() and not receipt.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=sorted(p for p in root.rglob('*') if p.is_file() and p.name!='MANIFEST.sha256')
(root/'MANIFEST.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(root))+'\n' for p in files))
files=sorted(p for p in root.rglob('*') if p.is_file())
for p in files:os.chmod(p,0o444)
for p in sorted((q for q in root.rglob('*') if q.is_dir()),reverse=True):os.chmod(p,0o555)
os.chmod(root,0o555)
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in files:
  info=zipfile.ZipInfo(root.name+'/'+str(p.relative_to(root)),(2026,10,4,0,0,0));info.create_system=3;info.external_attr=(stat.S_IFREG|0o444)<<16;info.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(archive) as z:
 assert len(z.namelist())==len(files)
 for p in files:assert z.read(root.name+'/'+str(p.relative_to(root)))==p.read_bytes()
for line in (root/'MANIFEST.sha256').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(root/p)==h
assert all(stat.S_IMODE(p.stat().st_mode)==0o444 for p in files)
assert all(stat.S_IMODE(p.stat().st_mode)==0o555 for p in [root]+list(q for q in root.rglob('*') if q.is_dir()))
result={'status':'PASS','audit':str(root/'AUDIT.md'),'audit_sha256':sha(root/'AUDIT.md'),'manifest_sha256':sha(root/'MANIFEST.sha256'),'archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,'payload_files':len(files)-1,'all_files_including_manifest':len(files),'read_only_files_and_directories':True,'source_manifest_sha256':'b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82','source_archive_sha256':'897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c','preservation_entries':1141}
receipt.write_text(json.dumps(result,indent=2)+'\n');os.chmod(archive,0o444);os.chmod(receipt,0o444)
print(json.dumps(result,indent=2))
