#!/usr/bin/env python3
"""Run an archived source experiment against pinned local predecessor packets.

No network access is used.  In the K219 archive the K220 packet is discovered
under portable/vendor; the K221 packet is inside K220.  Existing extracted
packets may instead be supplied explicitly.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,zipfile

HERE=Path(__file__).resolve().parent
K220_ARCHIVE='132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00'
K221_ARCHIVE='a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4'
INPUTS={
 'K220':{'machine/k220.native.tm':'4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4',
         'machine/sites220.json':'837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7'},
 'K221':{'machine/k221.native.tm':'e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc',
         'machine/sites221.json':'691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9'}}
DRIVERS=['additive_binder.py','constructor_binders.py','pair_binders.py','h_fusion.py',
         'nested_fourth_parameter.py','three_row_proposition.py','tag_permutations.py',
         'orientation_postfix.py','orientation_repair.py','nonlocal_reassociate.py',
         'protected_compile.py']

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def extract(archive,destination,expected):
    if sha(archive)!=expected:raise ValueError(f'Pinned archive mismatch: {archive}')
    destination.mkdir(parents=True,exist_ok=True);root=destination.resolve()
    with zipfile.ZipFile(archive)as z:
        for name in z.namelist():
            target=(root/name).resolve()
            if target!=root and root not in target.parents:raise ValueError('Unsafe archive member')
        z.extractall(root)

def validate(base,kind):
    for rel,want in INPUTS[kind].items():
        path=base/rel
        if not path.is_file()or sha(path)!=want:raise ValueError(f'Pinned {kind} input mismatch: {path}')

def main():
    if not __debug__ or sys.flags.optimize:raise ValueError('Assertions must be enabled; do not use python -O')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work',type=Path,default=Path.cwd()/'calculus_runs')
    ap.add_argument('--k220-archive',type=Path)
    ap.add_argument('--k220-base',type=Path)
    ap.add_argument('--k221-base',type=Path)
    ap.add_argument('driver',choices=DRIVERS)
    ap.add_argument('driver_args',nargs=argparse.REMAINDER)
    args=ap.parse_args();work=args.work.resolve();work.mkdir(parents=True,exist_ok=True)
    base=args.k220_base.resolve()if args.k220_base else None
    if base is None:
        archive=args.k220_archive.resolve()if args.k220_archive else None
        if archive is None:
            for p in HERE.parents:
                q=p/'portable/vendor/K220_Construction_2026-10-20.zip'
                if q.is_file():archive=q;break
        if archive is None:ap.error('No bundled K220 archive found; supply --k220-archive or --k220-base')
        extract(archive,work/'inputs',K220_ARCHIVE)
        base=work/'inputs/K220_Construction_2026-10-20'
    validate(base,'K220')
    parent=args.k221_base.resolve()if args.k221_base else None
    if parent is None:
        extract(base/'portable/vendor/K221_Construction_2026-10-20.zip',work/'inputs',K221_ARCHIVE)
        parent=work/'inputs/K221_Construction_2026-10-20'
    validate(parent,'K221')
    env=dict(os.environ,K220_BASE=str(base),K221_BASE=str(parent),CALCULUS_WORK_ROOT=str(work))
    command=[sys.executable,str(HERE/args.driver),*args.driver_args]
    provenance={'driver':args.driver,'driver_sha256':sha(HERE/args.driver),'argv':command,
                'python':sys.version,'K220_BASE':str(base),'K221_BASE':str(parent),
                'input_hashes':INPUTS,'scope':'Exploratory source/decoder search. Generated tables are not certified.'}
    (work/'run_provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    raise SystemExit(subprocess.run(command,env=env).returncode)

if __name__=='__main__':main()
