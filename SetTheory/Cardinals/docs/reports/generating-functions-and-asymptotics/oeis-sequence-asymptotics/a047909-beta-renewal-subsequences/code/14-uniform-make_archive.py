"""Create a deterministic, manifest-pinned ZIP from an explicit allowlist."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, zipfile
root=Path(__file__).resolve().parents[1]
files=[
'beta-renewal-uniform-addendum.pdf','beta-renewal-uniform-addendum.tex',
'README.md','SOURCES.md','VALIDATION.md','source-hashes.json',
'requirements.txt','build.sh','replay.sh',
'scripts/check_uniform.py','scripts/check_symbolic.py','scripts/check_inverse.py',
'scripts/validate_outputs.py','scripts/check_manifest.py','scripts/make_archive.py',
'checks/uniform.json','checks/symbolic.json','checks/inverse.json']
assert len(files)==len(set(files))
for name in files:
 p=PurePosixPath(name); f=root/name
 assert not p.is_absolute() and '..' not in p.parts and '\\' not in name
 assert f.is_file() and not f.is_symlink() and root in f.resolve().parents
manifest=''.join(hashlib.sha256((root/p).read_bytes()).hexdigest()+'  '+p+'\n' for p in sorted(files))
(root/'SHA256SUMS').write_text(manifest)
archive=root/'beta-renewal-uniform-reproducibility.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for name in sorted(files+['SHA256SUMS']):
  info=zipfile.ZipInfo('beta-renewal-uniform-addendum/'+name,date_time=(2026,10,2,0,0,0))
  info.compress_type=zipfile.ZIP_DEFLATED
  info.create_system=3
  info.external_attr=(stat.S_IFREG | 0o644)<<16
  z.writestr(info,(root/name).read_bytes())
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 assert len(z.namelist())==len(files)+1
 for info in z.infolist():
  p=PurePosixPath(info.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(info.external_attr>>16)
print(json.dumps({'archive':str(archive),'bytes':archive.stat().st_size,'members':len(files)+1,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest()},indent=2))
