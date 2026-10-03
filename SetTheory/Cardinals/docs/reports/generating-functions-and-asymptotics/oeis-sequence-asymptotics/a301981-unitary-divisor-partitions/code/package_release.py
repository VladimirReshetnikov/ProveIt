"""Generate strict content manifests and a deterministic, regular-file-only ZIP."""
from pathlib import Path
import argparse,hashlib,zipfile
base=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=base.parent/'unitary-partition-report.zip')
args=parser.parse_args()
if args.output.resolve().is_relative_to(base.resolve()):
    raise SystemExit("ZIP output must be outside the package directory")
def eligible(p):
    rel=p.relative_to(base)
    return (p.is_file() and rel.parts[0] not in ('.build','.replay')
            and '__pycache__' not in rel.parts and not any(part.startswith('.') for part in rel.parts))
def write_manifest(name,files):
    (base/name).write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(base).as_posix()+'\n' for p in sorted(files)))
files=[p for p in base.rglob('*') if eligible(p)]
for p in files:
    if p.is_symlink():raise SystemExit('Refusing symlink: '+str(p))
source=[p for p in files if p.name not in ('MANIFEST.sha256','SOURCE-MANIFEST.sha256')
        and p.suffix!='.pdf' and p.relative_to(base).parts[0]!='receipts']
write_manifest('SOURCE-MANIFEST.sha256',source)
files=[p for p in base.rglob('*') if eligible(p) and p.name!='MANIFEST.sha256']
write_manifest('MANIFEST.sha256',files)
files.append(base/'MANIFEST.sha256')
with zipfile.ZipFile(args.output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(files):
        info=zipfile.ZipInfo('unitary-partition-report/'+p.relative_to(base).as_posix(),(2026,10,2,0,0,0))
        info.external_attr=(0o100644<<16)
        info.compress_type=zipfile.ZIP_DEFLATED
        z.writestr(info,p.read_bytes())
print(f'{len(files)} regular files; SHA256 {hashlib.sha256(args.output.read_bytes()).hexdigest()}')
print(args.output)
