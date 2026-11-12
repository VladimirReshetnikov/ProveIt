"""Create the payload manifest and deterministic ZIP after validation."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
SKIP_SUFFIXES = {'.aux','.log','.out','.toc','.fls','.fdb_latexmk','.synctex.gz','.pyc'}


def keep(path):
    relative = path.relative_to(ROOT)
    if '__pycache__' in relative.parts:
        return False
    if relative.parts[0] == 'evidence':
        return True
    return path.suffix not in SKIP_SUFFIXES


files = sorted(p for p in ROOT.rglob('*') if p.is_file() and keep(p) and p.name!='MANIFEST.json')
manifest = {'algorithm':'SHA-256', 'files':[
    {'path':str(p.relative_to(ROOT)), 'bytes':p.stat().st_size,
     'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]}
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
files.append(ROOT/'MANIFEST.json')
target = ROOT.parent/(ROOT.name+'.zip')
with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
    for path in sorted(files):
        name = ROOT.name+'/'+str(path.relative_to(ROOT))
        item = zipfile.ZipInfo(name,date_time=(2026,11,10,12,0,0))
        item.compress_type = zipfile.ZIP_DEFLATED
        item.external_attr = 0o100644 << 16
        archive.writestr(item,path.read_bytes())
with zipfile.ZipFile(target) as archive:
    bad = archive.testzip()
    if bad:
        raise ValueError('ZIP CRC mismatch: '+bad)
print(json.dumps({'archive':str(target),'bytes':target.stat().st_size,
                  'members':len(files),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()},indent=2))
