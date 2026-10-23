#!/usr/bin/env python3
"""Fail-closed sealed integrity and isolated finite replay. No network or upstream execution."""
import sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('REJECT: optimized Python (-O/-OO) disables mathematical assertions.')
import argparse, hashlib, json, os, pathlib, shutil, subprocess, tempfile
R=pathlib.Path(__file__).resolve().parent

def require(condition,message):
    if not condition:raise SystemExit(message)

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def integrity():
    mf=R/'RELEASE_HASHES.json';require(mf.is_file(),'REJECT: missing manifest')
    manifest=json.loads(mf.read_text());require(isinstance(manifest,dict)and manifest,'REJECT: empty manifest')
    for p in R.rglob('*'):require(not p.is_symlink(),'REJECT: symbolic link in sealed release')
    actual={p.relative_to(R).as_posix()for p in R.rglob('*')if p.is_file()}
    require(actual==set(manifest)|{'RELEASE_HASHES.json'},'FILE SET FAILURE: missing='+repr(sorted(set(manifest)-actual))+'; unexpected='+repr(sorted(actual-set(manifest)-{'RELEASE_HASHES.json'})))
    for name,sha in manifest.items():
        q=pathlib.PurePosixPath(name);require(not q.is_absolute()and'..'not in q.parts,'REJECT: unsafe manifest path')
        require(digest(R/name)==sha,'HASH FAILURE: '+name)
    prov=json.loads((R/'PROVENANCE.json').read_text());blobs=prov['direct_source_blobs'];members=prov['retained_archive_members']
    for row in blobs:
        p=R/row['local_path'];raw=p.read_bytes();sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(sha==row['git_blob'],'SOURCE BLOB FAILURE: '+row['local_path'])
    for row in members:require(digest(R/row['local_path'])==row['sha256'],'SOURCE MEMBER FAILURE: '+row['local_path'])
    return len(manifest),len(blobs),len(members)

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--integrity-only',action='store_true');args=parser.parse_args()
    counts=integrity();print('INTEGRITY PASS: %s file hashes; %s direct source blobs; %s retained archive-member hashes.'%counts,flush=True)
    if args.integrity_only:return
    # Programs below were authored for this research iteration. Received
    # proof texts/data are inert; no inherited executable is imported.
    scripts=[
      'native/verify_native_tuple.py',
      'source/verify_selective_source.py',
      'source/check_sparse_popcount.py',
      'packing/verify_certificates.py',
      'review/check_new_local_adapters.py',
      'nine/check_ratio_tail.py',
      'nine/check_refined_majorant.py',
      'nine/verify_source_circuits.py',
      'audit/verify_majorant_independently.py',
      'audit/verify_nine_circuits_independently.py',
      'integer/verify_integer.py',
      'integer/check_local_lemmas.py',
      'positive/check_short.py',
      'short_audit/audit_short_independent.py',
    ]
    env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
    with tempfile.TemporaryDirectory(prefix='proveit-calibrated-replay-')as td:
        isolated=pathlib.Path(td)/'release';shutil.copytree(R,isolated)
        for name in scripts:
            print('CHECK '+name,flush=True)
            subprocess.run([sys.executable,'-B',str(isolated/name)],cwd=isolated,env=env,check=True)
    require(integrity()==counts,'REJECT: sealed original changed during isolated replay')
    print('PASS: %s independent/authored check programs in isolated copy.'%len(scripts),flush=True)
    print('Finite replay is not a consistency decision or a new end-to-end proof-assistant certificate.')
if __name__=='__main__':main()
