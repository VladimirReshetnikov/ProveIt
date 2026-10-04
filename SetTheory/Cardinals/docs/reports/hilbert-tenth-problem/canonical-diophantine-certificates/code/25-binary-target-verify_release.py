#!/usr/bin/env python3
"""Verify the complete Report 52 release against an externally trusted hash."""
import sys
if not sys.flags.isolated or sys.flags.optimize:
    raise SystemExit('Use python3 -I without -O')
import argparse,hashlib,json,os,stat
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PIN_BASE='a0458d81f2ec02b5c75d03c68d64da5a428bbf4304d69e4d94f82384fdb5958d'
PIN_AUDIT='dd6a27229d204f993b36e3f74a794353fa925e34926fd60fa3974eb1c50a33ab'
PIN_REPLAY='173afc73d4f0850d025e8e0d2f43c39fc23de50970b894d735f1497af23bd2d4'
def require(ok,why):
    if not ok: raise RuntimeError(why)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def files(root):
    out={}
    for p in sorted(root.rglob('*')):
        s=p.lstat();require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Nonregular release entry: '+str(p))
        if stat.S_ISREG(s.st_mode):out[p.relative_to(root).as_posix()]=p
    return out
def safechild(root,name):
    p=Path(name);require(isinstance(name,str) and name==p.as_posix() and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and name!='','Unsafe manifest path')
    return root/p
def verify_group(root,pins):
    for n,v in pins.items():
        p=safechild(root,n);require(p.is_file() and not p.is_symlink(),'Missing or unsafe file '+n)
        require(p.stat().st_size==v['bytes'] and digest(p)==v['sha256'],'Pin mismatch '+n)
        if 'mode' in v:require(stat.S_IMODE(p.stat().st_mode)==v['mode'],'Mode mismatch '+n)
def verify(trusted):
    require(len(trusted)==64 and all(c in '0123456789abcdef' for c in trusted),'Trusted lowercase SHA256 required')
    actual=files(ROOT);require('MANIFEST.json' in actual,'Missing manifest')
    require(digest(ROOT/'MANIFEST.json')==trusted,'Manifest SHA256 mismatch')
    m=json.loads((ROOT/'MANIFEST.json').read_text());require(m['schema']=='report52-inventory-v1','Wrong manifest schema')
    require(set(actual)==set(m['files'])|{'MANIFEST.json'},'Manifest inventory differs from release files')
    verify_group(ROOT,m['files'])
    b=ROOT/'baseline_report50';require(digest(b/'MANIFEST.json')==PIN_BASE,'Baseline manifest mismatch');bm=json.loads((b/'MANIFEST.json').read_text());require(set(files(b))==set(bm['files'])|{'MANIFEST.json'},'Baseline inventory mismatch');verify_group(b,bm['files'])
    a=ROOT/'independent_audit';require(digest(a/'audit-manifest.json')==PIN_AUDIT,'Scientific audit manifest mismatch');am=json.loads((a/'audit-manifest.json').read_text());verify_group(a,am['audit_files']);verify_group(ROOT/'science',am['source_files'])
    r=ROOT/'audit_replay';require(digest(r/'replay-pin-manifest.json')==PIN_REPLAY,'Replay manifest mismatch');rm=json.loads((r/'replay-pin-manifest.json').read_text());require(set(files(r))==set(rm['files'])|{'replay-pin-manifest.json'},'Replay inventory mismatch');verify_group(r,rm['files'])
    return {'schema':'report52-integrity-v1','status':'PASS','manifest_sha256':trusted,'release_files_including_manifest':len(actual),'baseline_authenticated':True,'scientific_audit_authenticated':True,'portable_replay_authenticated':True,'source_executables_run':False}
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);a=p.parse_args();print(json.dumps(verify(a.manifest_sha256),sort_keys=True,indent=2))
if __name__=='__main__':
    try:main()
    except Exception as e:print('Verification failed: '+str(e),file=sys.stderr);sys.exit(1)
