#!/usr/bin/env python3
"""Create an exact release ZIP, or safely extract/check one against this verified tree."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent


def need(ok,message):
    if not ok:
        raise RuntimeError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def verify(root,mode='--verify-only',optimized=False):
    result = subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),mode],capture_output=True,text=True,timeout=1800)
    need(result.returncode == 0,'Verifier failed: '+result.stderr[-2000:])
    return json.loads(result.stdout)


def identical(a,b):
    need(type(a) is type(b),'Archive replay receipt type mismatch')
    if type(b) is dict:
        need(set(a) == set(b),'Archive replay receipt keys mismatch')
        for k in b:identical(a[k],b[k])
    elif type(b) is list:
        need(len(a) == len(b),'Archive replay receipt list mismatch')
        for x,y in zip(a,b):identical(x,y)
    else:need(a == b,'Archive replay receipt value mismatch')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--create',type=Path)
    g.add_argument('--check',type=Path)
    p.add_argument('--sha256',help='required independently supplied archive checksum for --check')
    p.add_argument('--replay',action='store_true',help='full extracted replay under both normal and optimized verifiers')
    a = p.parse_args()
    baseline = verify(ROOT)
    need(baseline['release_stage'] == 'final','Only the final article release may be archived')
    files = {f.relative_to(ROOT).as_posix():f.read_bytes() for f in sorted(ROOT.rglob('*')) if f.is_file()}
    if a.create:
        target = a.create.resolve()
        need(target != ROOT and ROOT not in target.parents,'Archive must be external to release')
        need(not target.exists(),'Refusing to overwrite an existing archive')
        need(not a.sha256 and not a.replay,'Creation does not accept verification-only flags')
        with zipfile.ZipFile(target,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for name,raw in files.items():
                info = zipfile.ZipInfo(ROOT.name+'/'+name,date_time=(2026,10,3,0,0,0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = (stat.S_IFREG|0o644)<<16
                z.writestr(info,raw)
        verify(ROOT)
        print(json.dumps({'status':'CREATED','archive_filename':target.name,'archive_sha256':digest(target.read_bytes()),'archive_bytes':target.stat().st_size,'files':len(files)},indent=2,sort_keys=True))
        return
    need(a.sha256 is not None and len(a.sha256) == 64,'--check requires an externally supplied --sha256')
    need(digest(a.check.read_bytes()) == a.sha256,'Archive checksum mismatch')
    with zipfile.ZipFile(a.check) as z:
        infos = z.infolist()
        need(len(infos) == len(files),'Archive file count mismatch')
        names = [i.filename for i in infos]
        need(len(names) == len(set(names)),'Duplicate archive member')
        tops = set()
        contents = {}
        for info in infos:
            name = info.filename
            q = PurePosixPath(name)
            need(info.orig_filename == name and '\\' not in name and not q.is_absolute() and len(q.parts) >= 2,'Unsafe archive name')
            need(all(c not in ('','.','..') for c in name.split('/')),'Unsafe archive path component')
            need(not info.is_dir() and not info.flag_bits & 1,'Directory or encrypted archive member')
            mode = info.external_attr>>16
            need(stat.S_ISREG(mode),'Archive member is not a regular file')
            tops.add(q.parts[0]);relative = PurePosixPath(*q.parts[1:]).as_posix()
            need(relative in files and info.file_size == len(files[relative]),'Archive payload size/path mismatch')
            raw = z.read(info)
            need(raw == files[relative],'Archive payload bytes differ from verified tree')
            contents[relative] = raw
        need(len(tops) == 1 and set(contents) == set(files),'Archive exact root/path set mismatch')
    # Write only individually validated regular-file bytes; never extractall().
    with tempfile.TemporaryDirectory(prefix='report32-archive-') as tmp:
        work = Path(tmp)/'moved'/'fresh-extraction'
        for name,raw in contents.items():
            dest = work/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
        normal = verify(work)
        optimized = verify(work,optimized=True)
        identical(normal,optimized)
        records = {}
        if a.replay:
            for label,opt in [('normal',False),('optimized',True)]:
                records[label] = verify(work,'--replay',opt)
            identical(records['normal'],records['optimized'])
        verify(ROOT)
        print(json.dumps({'schema':'report32-archive-check-v1','status':'PASS','archive_filename':a.check.name,
                          'archive_sha256':a.sha256,'exact_archive_files':len(files),
                          'all_bytes_matched_verified_tree_before_extraction':True,'safe_regular_file_extraction':True,
                          'moved_extracted_identity_normal_optimized_equal':True,
                          'full_extracted_replay_performed':a.replay,'full_extracted_receipts':records},indent=2,sort_keys=True))

if __name__ == '__main__':main()
