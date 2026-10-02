#!/usr/bin/env python3
"""Create a deterministic ZIP and SHA-256 manifest of the final report tree."""
from pathlib import Path
import hashlib,json,zipfile
ROOT=Path(__file__).resolve().parent
EXCLUDED_DIRS={'.build','__pycache__','root-scale'}
EXCLUDED_FILES={'exact_counts','floating_counts'}
files=sorted(p for p in ROOT.rglob('*') if p.is_file() and not any(x in EXCLUDED_DIRS for x in p.relative_to(ROOT).parts) and p.name not in EXCLUDED_FILES and p != ROOT/'SHA256SUMS' and p.suffix not in {'.pyc'})
manifest=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()+'\n' for p in files)
(ROOT/'SHA256SUMS').write_text(manifest)
files.append(ROOT/'SHA256SUMS')
files.sort()
output=ROOT.with_suffix('.zip')
with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in files:
        name=ROOT.name+'/'+p.relative_to(ROOT).as_posix()
        info=zipfile.ZipInfo(name,date_time=(2026,10,2,0,0,0)); info.create_system=3
        info.external_attr=((0o755 if p.stat().st_mode&0o111 else 0o644)|0o100000)<<16
        info.compress_type=zipfile.ZIP_DEFLATED
        z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(output) as z:assert z.testzip() is None
release={'zip':str(output),'zip_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'archive_files':len(files),'bytes':output.stat().st_size,'manifest':'SHA256SUMS'}
ROOT.with_name(ROOT.name+'-release.json').write_text(json.dumps(release,indent=2)+'\n')
print(json.dumps(release,indent=2))
