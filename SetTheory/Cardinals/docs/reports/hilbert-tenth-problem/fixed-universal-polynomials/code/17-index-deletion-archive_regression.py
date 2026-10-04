#!/usr/bin/env python3
"""Reject malicious ZIP inventories using disposable external archives.

The supplied baseline archive and its independent SHA256 must first pass the
ordinary archive check. No arbitrary member is ever extracted by this script.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import stat
import struct
import subprocess
import sys
import tempfile
import warnings
import zipfile

ROOT=Path(__file__).resolve().parent


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def check(archive,digest,optimized=False):
    return subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(ROOT/'archive_release.py'),'--allow-engineering-preview','--check',str(archive),'--sha256',digest],capture_output=True,text=True,timeout=180)


def external_temp_parent():
    # Do not call tempfile.gettempdir(): its writable-directory probe can touch
    # the release itself when TMPDIR or the current directory is unsafe.
    candidates = [os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)]
    candidates += ['/tmp','/var/tmp']
    for value in candidates:
        candidate = Path(value).resolve()
        need(candidate != ROOT and ROOT not in candidate.parents, 'Temporary parent must be outside the release')
        if candidate.is_dir() and os.access(candidate, os.W_OK | os.X_OK):
            return candidate
    raise RuntimeError('No writable external temporary parent is available')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',required=True,type=Path)
    p.add_argument('--sha256',required=True)
    a=p.parse_args()
    for optimized in (False,True):
        baseline=check(a.archive,a.sha256,optimized)
        need(baseline.returncode==0,'Baseline archive failed: '+baseline.stderr)
    with zipfile.ZipFile(a.archive) as z:
        original=[(copy.copy(info),z.read(info)) for info in z.infolist()]
    cases=['duplicate-name','parent-traversal','absolute-name','backslash-name','symlink-mode','directory-member','unexpected-member','changed-bytes','missing-member','wrong-root','wrong-file-mode','unsupported-compression','nul-name','encrypted-member','wrong-declared-size']
    receipts=[]
    for optimized in (False,True):
        wrong=('0' if a.sha256[0]!='0' else '1')+a.sha256[1:]
        result=check(a.archive,wrong,optimized)
        need(result.returncode!=0 and 'Archive digest mismatch' in result.stderr,'Incorrect external archive digest accepted')
        receipts.append({'case':'incorrect-independent-digest','optimized':optimized,'rejected':True})
    with tempfile.TemporaryDirectory(prefix='report41-archive-tamper-',dir=external_temp_parent()) as tmp:
        for case in cases:
            rows=[(copy.copy(info),raw) for info,raw in original]
            info,raw=rows[0]
            if case=='duplicate-name':rows.append((copy.copy(info),raw))
            elif case=='parent-traversal':info.filename='Research_Report41/../outside'
            elif case=='absolute-name':info.filename='/unsafe-absolute-member'
            elif case=='backslash-name':info.filename='Research_Report41\\unsafe-member'
            elif case=='symlink-mode':info.external_attr=(stat.S_IFLNK|0o777)<<16
            elif case=='directory-member':info.filename+='/'
            elif case=='unexpected-member':
                extra=zipfile.ZipInfo('Research_Report41/unexpected-file');extra.create_system=3;extra.external_attr=(stat.S_IFREG|0o644)<<16;rows.append((extra,b'unexpected'))
            elif case=='changed-bytes':rows[0]=(info,raw+b'tamper')
            elif case=='missing-member':rows.pop()
            elif case=='wrong-root':info.filename='Other_Report/'+info.filename.split('/',1)[1]
            elif case=='wrong-file-mode':info.external_attr=(stat.S_IFREG|0o600)<<16
            elif case=='unsupported-compression':info.compress_type=zipfile.ZIP_BZIP2
            elif case=='nul-name':
                # ZipInfo truncates NUL names during construction: the resulting
                # wrong member name must still be rejected by exact inventory.
                info.filename='Research_Report41/unsafe\x00name'
            dest=Path(tmp)/(case+'.zip')
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                with zipfile.ZipFile(dest,'x') as z:
                    for member,data in rows:z.writestr(member,data)
            if case in ('encrypted-member','wrong-declared-size'):
                payload=bytearray(dest.read_bytes())
                with zipfile.ZipFile(dest) as written:
                    central=written.start_dir
                    local=written.infolist()[0].header_offset
                need(payload[central:central+4]==b'PK\x01\x02' and payload[local:local+4]==b'PK\x03\x04','ZIP mutation header missing')
                if case=='encrypted-member':
                    for offset in (central+8,local+6):
                        flags=struct.unpack_from('<H',payload,offset)[0]
                        struct.pack_into('<H',payload,offset,flags|1)
                else:
                    size=struct.unpack_from('<I',payload,central+24)[0]
                    struct.pack_into('<I',payload,central+24,size+1)
                dest.write_bytes(payload)
            digest=hashlib.sha256(dest.read_bytes()).hexdigest()
            for optimized in (False,True):
                result=check(dest,digest,optimized)
                need(result.returncode!=0,'Unsafe archive accepted: '+case)
                receipts.append({'case':case,'optimized':optimized,'rejected':True})
    print(json.dumps({'schema':'report41-archive-regression-v1','status':'PASS','cases':receipts,'baseline_sha256':a.sha256},indent=2,sort_keys=True))


if __name__=='__main__':main()
