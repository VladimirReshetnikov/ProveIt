#!/usr/bin/env python3
"""Fail-closed integrity and isolated finite replay for this mathematical release."""
import sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('REJECT: optimized Python (-O/-OO) disables mathematical assertions.')
import argparse, hashlib, json, os, pathlib, shutil, subprocess, tempfile
R=pathlib.Path(__file__).resolve().parent

def require(condition, message):
    if not condition: raise SystemExit(message)

def blob(path, expected):
    raw=path.read_bytes()
    require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==expected,
            'SOURCE BLOB FAILURE: '+str(path.relative_to(R)))

def integrity():
    manifest=json.loads((R/'RELEASE_HASHES.json').read_text())
    require(isinstance(manifest,dict) and manifest, 'Invalid empty manifest')
    for p in R.rglob('*'):
        require(not p.is_symlink(), 'REJECT: symbolic link in sealed release')
    actual={p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file()}
    require(actual==set(manifest)|{'RELEASE_HASHES.json'},
            'FILE SET FAILURE: missing='+repr(sorted(set(manifest)-actual))+
            '; unexpected='+repr(sorted(actual-set(manifest)-{'RELEASE_HASHES.json'})))
    for name,digest in manifest.items():
        q=pathlib.PurePosixPath(name)
        require(not q.is_absolute() and '..' not in q.parts, 'Invalid manifest path')
        require(hashlib.sha256((R/name).read_bytes()).hexdigest()==digest, 'HASH FAILURE: '+name)
    count=0
    current=json.loads((R/'review/SOURCE_PINS.json').read_text())
    for row in current['files']:
        blob(R/'review'/row['local_path'],row['blob_sha']);count+=1
    historical=json.loads((R/'inherited/SOURCE_PINS.json').read_text())
    for row in historical:
        blob(R/'inherited/sources'/row['package']/row['path'],row['sha']);count+=1
    post=json.loads((R/'review/postpin/SOURCE.json').read_text())
    for row in post['files']:
        blob(R/'review/postpin'/pathlib.PurePosixPath(row['path']).name,row['sha']);count+=1
    for row in json.loads((R/'inherited/ADDITIONAL_SOURCE_PINS.json').read_text()):
        blob(R/row['local_path'],row['blob_sha']);count+=1
    return len(manifest),count

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--integrity-only',action='store_true',help='Check bytes and source pins only; do not claim mathematical replay')
    args=ap.parse_args()
    files,pins=integrity()
    print(f'INTEGRITY PASS: {files} files; {pins} source blob checks.',flush=True)
    if args.integrity_only:return
    scripts=[
        'review/check_native_independently.py',
        'review/check_parent_coefficients.py',
        'packing/verify_certificate.py',
        'audit/verify_shared_source_symbolically.py',
        'nine/materialize_coefficients.py',
        'nine/verify_nine.py',
        'audit/verify_nine_independently.py',
        'integer/verify_integer.py',
        'positive/check_absorbed.py',
        'review/check_positive_leading_form.py',
        'review/check_variant_ledgers.py',
    ]
    env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
    with tempfile.TemporaryDirectory(prefix='proveit-sparse-release-') as td:
        target=pathlib.Path(td)/'release';shutil.copytree(R,target)
        for name in scripts:
            print('CHECK '+name,flush=True)
            subprocess.run([sys.executable,'-B',str(target/name)],cwd=target,env=env,check=True)
    # Check that none of the isolated scripts modified the sealed original.
    require(integrity()==(files,pins),'Original release changed during isolated replay')
    print(f'PASS: {files} file hashes, {pins} source blobs, {len(scripts)} isolated authored checks.')
    print('Finite replay passed. No consistency decision or new proof-assistant certificate is asserted.')

if __name__=='__main__':main()
