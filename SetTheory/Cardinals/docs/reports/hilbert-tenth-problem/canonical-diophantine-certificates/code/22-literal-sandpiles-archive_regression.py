#!/usr/bin/env python3
"""Reject malicious ZIP inventories using disposable external archives.

The supplied baseline archive and its independent SHA256 must first pass the
ordinary archive check. No arbitrary member is ever extracted by this script.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import warnings
import zipfile

ROOT=Path(__file__).resolve().parent


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def check(archive,digest):
    return subprocess.run([sys.executable,'-I','-B',str(ROOT/'archive_release.py'),'--check',str(archive),'--sha256',digest],capture_output=True,text=True,timeout=180)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',required=True,type=Path)
    p.add_argument('--sha256',required=True)
    a=p.parse_args()
    baseline=check(a.archive,a.sha256)
    need(baseline.returncode==0,'Baseline archive failed: '+baseline.stderr)
    with zipfile.ZipFile(a.archive) as z:
        original=[(copy.copy(info),z.read(info)) for info in z.infolist()]
    cases=['duplicate-name','parent-traversal','absolute-name','backslash-name','symlink-mode','directory-member','unexpected-member','changed-bytes','missing-member','wrong-root']
    receipts=[]
    with tempfile.TemporaryDirectory(prefix='report35-archive-tamper-') as tmp:
        for case in cases:
            rows=[(copy.copy(info),raw) for info,raw in original]
            info,raw=rows[0]
            if case=='duplicate-name':rows.append((copy.copy(info),raw))
            elif case=='parent-traversal':info.filename='Research_Report35/../outside'
            elif case=='absolute-name':info.filename='/unsafe-absolute-member'
            elif case=='backslash-name':info.filename='Research_Report35\\unsafe-member'
            elif case=='symlink-mode':info.external_attr=(stat.S_IFLNK|0o777)<<16
            elif case=='directory-member':info.filename+='/'
            elif case=='unexpected-member':
                extra=zipfile.ZipInfo('Research_Report35/unexpected-file');extra.create_system=3;extra.external_attr=(stat.S_IFREG|0o644)<<16;rows.append((extra,b'unexpected'))
            elif case=='changed-bytes':rows[0]=(info,raw+b'tamper')
            elif case=='missing-member':rows.pop()
            else:info.filename='Other_Report/'+info.filename.split('/',1)[1]
            dest=Path(tmp)/(case+'.zip')
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                with zipfile.ZipFile(dest,'x') as z:
                    for member,data in rows:z.writestr(member,data)
            digest=hashlib.sha256(dest.read_bytes()).hexdigest()
            result=check(dest,digest)
            need(result.returncode!=0,'Unsafe archive accepted: '+case)
            receipts.append({'case':case,'rejected':True})
    print(json.dumps({'schema':'report35-archive-regression-v1','status':'PASS','cases':receipts,'baseline_sha256':a.sha256},indent=2,sort_keys=True))


if __name__=='__main__':main()
