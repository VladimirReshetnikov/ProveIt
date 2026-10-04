"""Freeze only this review-owned dossier and bind its bytes with two inventories."""
from pathlib import Path
import os,json,hashlib,stat
root=Path(__file__).resolve().parent.parent
files=sorted(p for p in root.rglob('*') if p.is_file() and p not in (root/'MANIFEST.json',root/'SHA256SUMS'))
manifest={'review_type':'independent model-performed manuscript and visual review','verdict':'accepted within explicit theorem-dependency and exact-model scope','final_tex_sha256':'870025b5d7f633890db20ae3d166deeafcf83657f7fc4746ad221aa933719857','final_pdf_sha256':'729213d2a1b3cab8bd00912a0bbdc8a035ebd26c4e4af22da4aab5e5e2b89bf8','manifest_exclusions':['MANIFEST.json','SHA256SUMS'],'entries':[{'path':str(p.relative_to(root)),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'frozen_mode':'0444'} for p in files]}
(root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
all_files=sorted(p for p in root.rglob('*') if p.is_file() and p!=root/'SHA256SUMS')
(root/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))+'\n' for p in all_files))
for p in root.rglob('*'):
    if p.is_file(): p.chmod(0o444)
for p in sorted((p for p in root.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True): p.chmod(0o555)
root.chmod(0o555)
for entry in manifest['entries']:
    p=root/entry['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256']
assert len(files)+2==len([p for p in root.rglob('*') if p.is_file()])
assert all(stat.S_IMODE(p.stat().st_mode)==(0o555 if p.is_dir() else 0o444) for p in [root,*root.rglob('*')])
print(json.dumps({'frozen':True,'files':len(all_files)+1,'manifest_entries':len(files),'hashes':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in ['README.md','CHECKS.md','VISUAL_REVIEW.md','MANIFEST.json','SHA256SUMS']}},indent=2))
