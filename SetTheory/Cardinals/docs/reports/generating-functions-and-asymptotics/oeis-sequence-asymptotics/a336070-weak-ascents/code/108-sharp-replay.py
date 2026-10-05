#!/usr/bin/env python3
"""Fresh ZIP replay. Writes only into a new user-selected output directory."""
import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
from zipfile import ZipFile


def require(ok, message):
    if not ok: raise RuntimeError(message)

def digest(p): return sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent/'report108_source_checks.zip')
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args(); require(not args.out.exists(), 'Replay output must not already exist')
    args.out.mkdir(parents=True)
    with ZipFile(args.archive) as z:
        names=z.namelist(); require(len(names)==len(set(names)), 'Duplicate archive member')
        for name in names:
            p=PurePosixPath(name)
            require(name.startswith('report108/') and not p.is_absolute() and '..' not in p.parts and '\\' not in name, 'Unsafe archive member')
            require((z.getinfo(name).external_attr>>16)&0o170000 != 0o120000, 'Archive symlink is forbidden')
        manifest=json.loads(z.read('report108/manifest.json'))
        expected={'report108/'+r['path'] for r in manifest['files']}|{'report108/manifest.json'}
        require(set(names)==expected, 'Archive membership differs from manifest')
        z.extractall(args.out)
    root=(args.out/'report108').resolve(); before=digest(root/'report108.pdf'); tex_before=digest(root/'report108.tex')
    commands=[ [sys.executable,'verify_package.py'], [sys.executable,'-O','verify_package.py'],
               [sys.executable,'checks/run_checks.py'], ['bash','build.sh'],
               [sys.executable,'verify_package.py'] ]
    results=[]
    for index,cmd in enumerate(commands,1):
        cp=subprocess.run(cmd,cwd=root,text=True,capture_output=True)
        (args.out/f'step{index}.stdout').write_text(cp.stdout)
        (args.out/f'step{index}.stderr').write_text(cp.stderr)
        require(cp.returncode==0,f'Replay step {index} failed: {cmd}; see logs')
        results.append({'command':cmd,'returncode':cp.returncode})
    require(digest(root/'report108.pdf')==before,'Regenerated final PDF differs')
    require(digest(root/'report108.tex')==tex_before,'Assembled standalone TeX differs')
    result={'status':'passed','archive_sha256':digest(args.archive),'pdf_sha256':before,
            'tex_sha256':tex_before,'fresh_extraction':str(root),'byte_identical_pdf':True,'byte_identical_tex':True,'steps':results}
    (args.out/'replay_result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
