#!/usr/bin/env python3
"""Create deterministic Report35 ZIPs, or safely check and replay a supplied ZIP."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parent
ARCHIVE_ROOT='Research_Report35'


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def verify(root,mode='--verify-only',optimized=False):
    done=subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),mode],capture_output=True,text=True,timeout=7200)
    need(done.returncode==0,'Verifier failed: '+done.stderr[-3000:])
    return json.loads(done.stdout)


def typed_equal(a,b):
    need(type(a) is type(b),'Archive receipt type mismatch')
    if type(b) is dict:
        need(set(a)==set(b),'Archive receipt keys mismatch')
        for k in b:typed_equal(a[k],b[k])
    elif type(b) is list:
        need(len(a)==len(b),'Archive receipt length mismatch')
        for x,y in zip(a,b):typed_equal(x,y)
    else:need(a==b,'Archive receipt value mismatch')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--create',type=Path)
    g.add_argument('--check',type=Path)
    p.add_argument('--sha256',help='independently supplied archive digest, required with --check')
    p.add_argument('--replay',action='store_true')
    a=p.parse_args()
    identity=verify(ROOT)
    need(identity['release_stage']=='final','Only a final article release can be archived')
    files={p.relative_to(ROOT).as_posix():p.read_bytes() for p in sorted(ROOT.rglob('*')) if p.is_file()}
    modes={name:stat.S_IMODE((ROOT/name).stat().st_mode) for name in files}
    if a.create:
        dest=a.create.resolve()
        need(dest!=ROOT and ROOT not in dest.parents,'Archive must be external')
        need(not dest.exists(),'Refusing to overwrite an existing archive')
        need(not a.sha256 and not a.replay,'Check-only options on create')
        with zipfile.ZipFile(dest,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for name,raw in files.items():
                info=zipfile.ZipInfo(ARCHIVE_ROOT+'/'+name,date_time=(2026,10,3,0,0,0))
                info.create_system=3;info.compress_type=zipfile.ZIP_DEFLATED
                info.external_attr=(stat.S_IFREG|modes[name])<<16
                z.writestr(info,raw,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
        verify(ROOT)
        print(json.dumps({'schema':'report35-archive-create-v1','status':'CREATED','archive_filename':dest.name,'archive_sha256':sha(dest.read_bytes()),'archive_bytes':dest.stat().st_size,'file_count':len(files)},indent=2,sort_keys=True))
        return
    need(type(a.sha256) is str and re.fullmatch('[0-9a-f]{64}',a.sha256) is not None,'Check requires an independent SHA256')
    need(sha(a.check.read_bytes())==a.sha256,'Archive digest mismatch')
    contents={}
    with zipfile.ZipFile(a.check) as z:
        infos=z.infolist();names=[i.filename for i in infos]
        need(len(infos)==len(files) and len(names)==len(set(names)),'Archive duplicate/count mismatch')
        for info in infos:
            name=info.filename;q=PurePosixPath(name)
            need(info.orig_filename==name and '\\' not in name and not q.is_absolute(),'Unsafe archive name')
            need(all(v not in ('','.','..') for v in name.split('/')) and len(q.parts)>=2,'Unsafe archive component')
            need(q.parts[0]==ARCHIVE_ROOT,'Unexpected archive root')
            rel=PurePosixPath(*q.parts[1:]).as_posix()
            need(not info.is_dir() and not info.flag_bits&1,'Directory/encrypted member')
            mode=info.external_attr>>16
            need(stat.S_ISREG(mode) and stat.S_IMODE(mode)==modes.get(rel),'Nonregular/mode mismatch')
            need(rel in files and info.file_size==len(files[rel]),'Unexpected member/size')
            raw=z.read(info)
            need(raw==files[rel],'Archive payload differs from verified tree')
            contents[rel]=raw
    need(set(contents)==set(files),'Archive exact inventory mismatch')
    with tempfile.TemporaryDirectory(prefix='report35-archive-') as tmp:
        work=Path(tmp)/'moved'/'fresh-extraction';work.mkdir(parents=True)
        work.chmod(0o755)
        for name,raw in contents.items():
            dest=work/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);dest.chmod(modes[name])
        for p in work.rglob('*'):
            if p.is_dir():p.chmod(0o755)
        normal=verify(work);optimized=verify(work,optimized=True);typed_equal(normal,optimized)
        receipts={}
        if a.replay:
            for label,opt in [('normal',False),('optimized',True)]:receipts[label]=verify(work,'--replay',opt)
            typed_equal(receipts['normal'],receipts['optimized'])
        verify(ROOT)
        print(json.dumps({'schema':'report35-archive-check-v1','status':'PASS','archive_filename':a.check.name,'archive_sha256':a.sha256,'exact_files':len(files),'safe_regular_file_extraction':True,'all_bytes_matched_before_extraction':True,'extracted_identity_normal_optimized_equal':True,'full_replay':a.replay,'receipts':receipts},indent=2,sort_keys=True))


if __name__=='__main__':main()
