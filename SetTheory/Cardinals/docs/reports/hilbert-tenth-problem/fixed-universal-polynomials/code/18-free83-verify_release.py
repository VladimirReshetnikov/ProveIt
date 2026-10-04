#!/usr/bin/env python3
"""Authenticate an exact release inventory, then replay only the new report checker."""
import argparse, hashlib, json, re, stat, subprocess, sys
from pathlib import Path, PurePosixPath

ROOT=Path(__file__).resolve().parent
def need(ok,message):
    if not ok: raise RuntimeError(message)
def authenticate(root, expected):
    need(bool(re.fullmatch('[0-9a-f]{64}',expected)), 'A trusted manifest SHA256 is required')
    raw=(root/'MANIFEST.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest()==expected,'Manifest digest mismatch')
    manifest=json.loads(raw)
    need(manifest.get('schema')=='report43-release-v1','Manifest schema')
    entries=manifest['files'];need(type(entries) is dict and entries,'Empty inventory')
    actual=set()
    for path in root.rglob('*'):
        mode=path.lstat().st_mode
        need(stat.S_ISREG(mode) or stat.S_ISDIR(mode),'Nonregular release object')
        if path.is_file():actual.add(path.relative_to(root).as_posix())
    need(actual==set(entries)|{'MANIFEST.json'},'Missing or extra release files')
    for name,record in entries.items():
        logical=PurePosixPath(name)
        need(not logical.is_absolute() and '..' not in logical.parts and logical.as_posix()==name,'Unsafe inventory path')
        need(type(record['bytes']) is int and record['bytes']>=0,'Invalid byte length')
        data=(root/name).read_bytes()
        need(len(data)==record['bytes'] and hashlib.sha256(data).hexdigest()==record['sha256'],'File mismatch: '+name)
    sources=json.loads((root/'SOURCE_INVENTORY.json').read_text())
    for name,record in sources['files'].items():
        need(name in entries and entries[name]['sha256']==record['sha256'],'Source inventory mismatch')
    return manifest
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256',required=True)
    parser.add_argument('--verify-only',action='store_true')
    args=parser.parse_args()
    manifest=authenticate(ROOT,args.manifest_sha256)
    output={'status':'PASS','authenticated_files':len(manifest['files']),
            'manifest_sha256':args.manifest_sha256,'ordinary_input_language':'OPEN'}
    if not args.verify_only:
        command=[sys.executable,'-I','-B']
        if sys.flags.optimize:command.append('-O')
        command.append(str(ROOT/'check_math.py'))
        result=subprocess.run(command,cwd=ROOT.parent,capture_output=True,text=True,timeout=180)
        need(result.returncode==0,'New report checker failed: '+result.stderr)
        expected=(ROOT/'checks/MATH.normal.json').read_text()
        need(result.stdout==expected,'Math receipt mismatch')
        output['new_report_math_receipt_matches']=True
        authenticate(ROOT,args.manifest_sha256)
    print(json.dumps(output,sort_keys=True,indent=2))
if __name__=='__main__':main()
