#!/usr/bin/env python3
"""Recover all82 delivered members from exact placements and immutable arrival.
This validates only Git blob identities, never a delivered checksum manifest,
and does not execute any recovered code. The output directory must be new.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import zipfile

def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=Path.cwd())
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--map',type=Path)
    args=ap.parse_args()
    repo=Path(subprocess.check_output(['git','-C',str(args.repo),'rev-parse','--show-toplevel'],text=True).strip())
    mapping=args.map or repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake204-placement.json'
    plan=json.loads(mapping.read_text())
    raw=subprocess.check_output(['git','-C',str(repo),'show',plan['arrival_commit']+':'+plan['arrival_archive']])
    if blob(raw)!=plan['archive_git_blob']:
        raise SystemExit('Arrival Git blob changed')
    archive=zipfile.ZipFile(io.BytesIO(raw))
    output=args.out.resolve()
    if output.exists():
        raise SystemExit('Output directory must be new')
    files=[]
    for row in plan['members']:
        member=Path(row['member'])
        if member.is_absolute() or '..' in member.parts:
            raise SystemExit('Unsafe member path')
        delivered=archive.read(plan['archive_wrapper']+row['member'])
        if row['destination']:
            destination=Path(row['destination'])
            if destination.is_absolute() or '..' in destination.parts:
                raise SystemExit('Unsafe placement path')
            data=(repo/destination).read_bytes()
            if data!=delivered:
                raise SystemExit('Placed bytes changed: '+str(destination))
        else:
            data=delivered
        if len(data)!=row['bytes'] or blob(data)!=row['git_blob']:
            raise SystemExit('Member Git blob mismatch: '+str(member))
        files.append((member,data))
    if len(files)!=82 or len({p for p,_ in files})!=82:
        raise SystemExit('Incomplete or repeated member list')
    output.mkdir(parents=True)
    for member,data in files:
        target=output/member
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data)
    print('Recovered82 exact members. No delivered code executed.')

if __name__=='__main__':
    main()
