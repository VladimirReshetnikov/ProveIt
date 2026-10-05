#!/usr/bin/env python3
"""Validate a fresh archive extraction, then rebuild and compare the PDF."""
from hashlib import sha256
from pathlib import Path, PurePosixPath
from zipfile import ZipFile
import argparse
import json
import subprocess
import sys

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive',type=Path,default=Path(__file__).resolve().parent/'report111_source_checks.zip')
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    require(not args.out.exists(),'replay destination must not already exist')
    args.out.mkdir(parents=True)
    archive_hash=digest(args.archive)
    with ZipFile(args.archive) as archive:
        names=archive.namelist()
        require(len(names)==len(set(names)),'duplicate archive member')
        for name in names:
            p=PurePosixPath(name)
            require(name.startswith('report111/') and not p.is_absolute() and '..' not in p.parts and '\\' not in name,
                    'unsafe archive member')
            require((archive.getinfo(name).external_attr>>16)&0o170000!=0o120000,'symlink member forbidden')
        manifest=json.loads(archive.read('report111/manifest.json'))
        expected={'report111/'+p for p in manifest['files']}|{'report111/manifest.json'}
        require(set(names)==expected,'archive inventory differs from manifest')
        archive.extractall(args.out)
    root=(args.out/'report111').resolve()
    original_pdf=digest(root/'report111.pdf')
    commands=[[sys.executable,'integrity.py'],[sys.executable,'-O','integrity.py'],
              [sys.executable,'checks/verify_report111.py'],[sys.executable,'-O','checks/verify_report111.py'],
              [sys.executable,'checks/mutation_campaign.py'],[sys.executable,'-O','checks/mutation_campaign.py'],
              [sys.executable,'integrity_corruption_test.py'],[sys.executable,'-O','integrity_corruption_test.py'],
              [sys.executable,'build.py'],[sys.executable,'integrity.py']]
    for index,command in enumerate(commands,1):
        cp=subprocess.run(command,cwd=root,text=True,capture_output=True)
        (args.out/f'step{index}.stdout').write_text(cp.stdout)
        (args.out/f'step{index}.stderr').write_text(cp.stderr)
        require(cp.returncode==0,f'replay step {index} failed; inspect replay logs')
    require(digest(root/'report111.pdf')==original_pdf,'rebuilt PDF differs from packaged PDF')
    require(digest(args.archive)==archive_hash,'archive changed during replay')
    result={'status':'PASS','steps':len(commands),'pdf_byte_identical':True,
            'archive_sha256':archive_hash,'pdf_sha256':original_pdf}
    (args.out/'replay_result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
