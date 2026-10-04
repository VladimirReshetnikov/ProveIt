#!/usr/bin/env python3
"""Authenticate inert release files and create deterministic external ZIPs.
Commands: check-inputs; manifest --output NEW; verify --manifest-sha256 PIN;
archive --manifest-sha256 PIN --output NEW. Use python3 -I -S -B.
The manifest digest must be obtained through a trusted separate channel.
"""
import argparse, hashlib, json, os, re, stat, sys, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
MANIFEST='RELEASE_MANIFEST.json'
INPUT_PINS_SHA256='331e5276ac4375faa6aed52766b762dad28135e37d16361cf376d5bef1ff0615'

def require(test,message):
    if not test: raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def encoded(value):return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
def unique_object(pairs):
    out={}
    for key,value in pairs:
        require(key not in out,'Duplicate JSON key');out[key]=value
    return out
def parse(data):return json.loads(data,object_pairs_hook=unique_object)
def regular_bytes(path):
    first=path.lstat()
    require(stat.S_ISREG(first.st_mode) and first.st_nlink==1,'Expected single-link regular file: '+str(path))
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
    with os.fdopen(fd,'rb') as stream:
        before=os.fstat(stream.fileno());data=stream.read();after=os.fstat(stream.fileno())
    last=path.lstat()
    def identity(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_nlink,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
    require(identity(first)==identity(before)==identity(after)==identity(last),'Input changed while reading: '+str(path))
    return data

def inventory(include_manifest=False):
    require(stat.S_ISDIR(ROOT.lstat().st_mode),'Release root is not a directory')
    result={};payload={}
    for path in sorted(ROOT.rglob('*')):
        st=path.lstat();rel=path.relative_to(ROOT).as_posix()
        require(all(ord(c)>=32 and c not in '\\' for c in rel),'Unsafe archive name')
        require(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),'Nonregular release entry: '+rel)
        if stat.S_ISREG(st.st_mode) and (include_manifest or rel!=MANIFEST):
            data=regular_bytes(path);payload[rel]=data;result[rel]={'bytes':len(data),'sha256':sha(data)}
    observed_dirs={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if stat.S_ISDIR(p.lstat().st_mode)}
    expected_dirs={parent.as_posix() for name in result for parent in Path(name).parents if parent.as_posix()!='.'}
    require(observed_dirs==expected_dirs,'Unexpected empty directory in release')
    return result,payload

def new_output(raw):
    require(raw.startswith('/') and not raw.startswith('//'),'Canonical absolute output required')
    path=Path(raw)
    require(str(path)==raw and all(part not in ('.','..') for part in raw.split('/')),'Noncanonical output path')
    for ancestor in reversed([path,*path.parents]):
        if os.path.lexists(ancestor):
            st=ancestor.lstat();require(not stat.S_ISLNK(st.st_mode),'Symlink output component')
            require(ancestor==path or stat.S_ISDIR(st.st_mode),'Output ancestor is not a directory')
        else:require(ancestor==path,'Output parent must exist')
    require(not os.path.lexists(path),'Output exists')
    require(path!=ROOT and ROOT not in path.parents and path not in ROOT.parents,'Output must be external to release')
    return path

def check_inputs():
    raw=regular_bytes(ROOT/'INPUT_PINS.json')
    require(sha(raw)==INPUT_PINS_SHA256,'Input-pin map differs from reviewed version')
    pins=parse(raw);require(set(pins)=={'files','roots'},'Invalid input-pin schema')
    allfiles,_=inventory()
    scopes={Path(root).parts[0] for root in pins['roots']}
    actual={name:value for name,value in allfiles.items() if any(name.startswith(root+'/') for root in scopes)}
    require(actual==pins['files'],'Frozen input inventory/hash mismatch')
    return len(actual)

def verify(pin):
    require(re.fullmatch('[0-9a-f]{64}',pin) is not None,'A lowercase SHA-256 manifest pin is required')
    raw=regular_bytes(ROOT/MANIFEST);require(sha(raw)==pin,'Manifest digest mismatch')
    manifest=parse(raw)
    require(isinstance(manifest,dict) and set(manifest)=={'format','files'} and manifest['format']=='Report60 release manifest v1','Invalid manifest schema')
    files,payload=inventory();require(files==manifest['files'],'Release inventory/hash mismatch')
    for name,row in manifest['files'].items():
        require(isinstance(name,str) and isinstance(row,dict) and set(row)=={'bytes','sha256'},'Invalid manifest entry')
        require(type(row['bytes']) is int and row['bytes']>=0 and isinstance(row['sha256'],str) and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'Invalid manifest value')
    check_inputs()
    payload[MANIFEST]=raw
    return files,payload

def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'Use python3 -I -S -B without optimization')
    require(Path(__file__).absolute()==Path(__file__).resolve(),'Tool path must have no symlink components')
    ap=argparse.ArgumentParser(description=__doc__);sub=ap.add_subparsers(dest='command',required=True)
    sub.add_parser('check-inputs')
    p=sub.add_parser('manifest');p.add_argument('--output',required=True)
    p=sub.add_parser('verify');p.add_argument('--manifest-sha256',required=True)
    p=sub.add_parser('archive');p.add_argument('--manifest-sha256',required=True);p.add_argument('--output',required=True)
    a=ap.parse_args()
    if a.command=='check-inputs':
        print(encoded({'status':'PASS','frozen_files':check_inputs()}).decode());return
    if a.command=='manifest':
        check_inputs();files,_=inventory();data=encoded({'format':'Report60 release manifest v1','files':files})
        out=new_output(a.output)
        with out.open('xb') as stream:stream.write(data)
        require(inventory()[0]==files,'Release changed during manifest generation')
        print(encoded({'status':'PASS','manifest_sha256':sha(data),'files':len(files),'output':str(out)}).decode());return
    files,payload=verify(a.manifest_sha256)
    if a.command=='verify':
        print(encoded({'status':'PASS','manifest_sha256':a.manifest_sha256,'files':len(files)}).decode());return
    out=new_output(a.output)
    with out.open('xb') as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9,strict_timestamps=True) as archive:
            for name,data in sorted(payload.items()):
                entry=zipfile.ZipInfo('Report60/'+name,date_time=(2026,10,4,0,0,0));entry.create_system=3
                entry.external_attr=(stat.S_IFREG|0o644)<<16;entry.compress_type=zipfile.ZIP_DEFLATED
                archive.writestr(entry,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    require(inventory()[0]==files and regular_bytes(ROOT/MANIFEST)==payload[MANIFEST],'Release changed during archive generation')
    with zipfile.ZipFile(out) as archive:
        require(archive.testzip() is None,'ZIP CRC failure')
        require(archive.namelist()==['Report60/'+name for name in sorted(payload)],'ZIP entry mismatch')
        require(all(archive.read('Report60/'+name)==data for name,data in payload.items()),'ZIP content mismatch')
    data=regular_bytes(out)
    print(encoded({'status':'PASS','files':len(payload),'manifest_sha256':a.manifest_sha256,'zip_sha256':sha(data),'bytes':len(data),'output':str(out)}).decode())
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,zipfile.BadZipFile) as error:
        print('RELEASE REFUSED: '+str(error),file=sys.stderr);raise SystemExit(2)
