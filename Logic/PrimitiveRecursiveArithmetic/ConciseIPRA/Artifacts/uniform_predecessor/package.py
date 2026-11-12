"""Create an exact payload manifest and deterministic delivery ZIP."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parent

def included(path):
    return (path.is_file() and '__pycache__' not in path.parts
            and path.suffix not in ('.pyc','.aux','.log','.out','.toc')
            and path.name!='MANIFEST.json')

def main():
    paths=sorted(p for p in ROOT.rglob('*') if included(p))
    rows=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,
           'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]
    (ROOT/'MANIFEST.json').write_text(json.dumps({'algorithm':'SHA-256','files':rows},indent=2)+'\n')
    paths.append(ROOT/'MANIFEST.json')
    target=ROOT.parent/(ROOT.name+'.zip')
    with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for path in sorted(paths):
            info=zipfile.ZipInfo(ROOT.name+'/'+path.relative_to(ROOT).as_posix(),(2026,11,10,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=0o100644<<16
            archive.writestr(info,path.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    print(target)
    print('files:',len(paths),'bytes:',target.stat().st_size,'sha256:',hashlib.sha256(target.read_bytes()).hexdigest())

if __name__=='__main__':
    main()
