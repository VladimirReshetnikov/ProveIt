#!/usr/bin/env python3
"""Portable, fail-closed replay of the frozen independent chronological audit.
Executes only byte-pinned independent checkers copied into a NEW external output.
No science builder, author checker, predecessor code, or saved schedule executes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys

AUDIT_MANIFEST_SHA256='6a646bda78f0f3cc29150fd562292b138231879dedfd5e149117ed6d4c8a14e9'
SCIENCE_MANIFEST_SHA256='461b53aa2a95c42071d33ede3ad9f4ea6431b63f5cc2633f8d94f39da6fc52d8'
RECEIPT_NAMES=('source-audit-receipt.json','interface-audit-receipt.json')

class ReplayError(Exception): pass
def require(condition,message):
    if not condition: raise ReplayError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def strict_object(items):
    out={}
    for key,value in items:
        require(key not in out,'duplicate JSON key: '+key)
        out[key]=value
    return out
def parse(data):
    return json.loads(data.decode('utf-8'),object_pairs_hook=strict_object,
                      parse_constant=lambda x: (_ for _ in ()).throw(ReplayError('nonfinite JSON: '+x)))
def encoded(value): return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode('utf-8')
def relative_name(name):
    require(type(name) is str and bool(name),'invalid manifest path')
    p=PurePosixPath(name)
    require(not p.is_absolute() and str(p)==name and all(c not in ('','.','..') for c in p.parts),
            'unsafe manifest path: '+name)
    return name

def checked_path(raw,must_exist):
    require(bool(raw),'empty path')
    p=Path(raw)
    require(p.is_absolute(),'paths must be absolute: '+raw)
    require('..' not in p.parts,'parent traversal is forbidden: '+raw)
    current=Path(p.anchor)
    for number,part in enumerate(p.parts[1:],1):
        current=current/part
        is_leaf=number==len(p.parts)-1
        try: st=current.lstat()
        except FileNotFoundError:
            require(is_leaf and not must_exist,'missing path or parent: '+str(current))
            continue
        require(not stat.S_ISLNK(st.st_mode),'symlink path component: '+str(current))
        require(stat.S_ISDIR(st.st_mode),'path component is not a directory: '+str(current))
        if is_leaf and not must_exist: raise ReplayError('output already exists: '+str(p))
    require(p!=Path(p.anchor),'filesystem root cannot be an input/output')
    return p

def below(path,parent): return path==parent or parent in path.parents

def read_regular(path):
    checked_path(str(path.parent),True)
    before=path.lstat()
    require(stat.S_ISREG(before.st_mode) and not stat.S_ISLNK(before.st_mode),'not a regular nonsymlink file: '+str(path))
    flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)
    fd=os.open(str(path),flags)
    try:
        opened=os.fstat(fd)
        require((opened.st_dev,opened.st_ino)==(before.st_dev,before.st_ino),'file changed while opening: '+str(path))
        with os.fdopen(fd,'rb',closefd=False) as stream: data=stream.read()
        after=os.fstat(fd)
        require((after.st_size,after.st_mtime_ns)==(opened.st_size,opened.st_mtime_ns),'file changed while reading: '+str(path))
    finally: os.close(fd)
    return data,(before.st_mode,before.st_size,before.st_mtime_ns,before.st_dev,before.st_ino)

def inventory(records,extra_name,extra_bytes):
    require(type(records) is list,'manifest inventory must be a list')
    result={}
    for r in records:
        require(type(r) is dict and set(r)=={'path','bytes','sha256'},'invalid inventory entry')
        name=relative_name(r['path'])
        require(name not in result and type(r['bytes']) is int and r['bytes']>=0,'duplicate/invalid inventory entry')
        require(type(r['sha256']) is str and len(r['sha256'])==64 and all(c in '0123456789abcdef' for c in r['sha256']),'invalid digest')
        result[name]=(r['bytes'],r['sha256'])
    require(extra_name not in result,'manifest self-entry is not permitted')
    result[extra_name]=(len(extra_bytes),sha(extra_bytes))
    return result

def read_tree(root,expected):
    expected_dirs={'.'}
    for name in expected:
        for parent in PurePosixPath(name).parents:
            expected_dirs.add(str(parent))
    files=set();dirs=set();data={};metadata={}
    for base,children,names in os.walk(root,followlinks=False):
        base=Path(base);rel=str(base.relative_to(root));dirs.add(rel)
        st=base.lstat()
        require(stat.S_ISDIR(st.st_mode) and not stat.S_ISLNK(st.st_mode),'unsafe directory: '+str(base))
        metadata[rel+'/']=(st.st_mode,st.st_size,st.st_mtime_ns,st.st_dev,st.st_ino)
        for child in children:
            st=(base/child).lstat()
            require(stat.S_ISDIR(st.st_mode) and not stat.S_ISLNK(st.st_mode),'symlink/non-directory child: '+str(base/child))
        for name in names:
            path=base/name;relname=path.relative_to(root).as_posix();files.add(relname)
            require(relname in expected,'unmanifested input file: '+relname)
            contents,stamp=read_regular(path)
            size,digest=expected[relname]
            require(len(contents)==size and sha(contents)==digest,'tampered input: '+relname)
            data[relname]=contents;metadata[relname]=stamp
    require(files==set(expected),'missing input files: '+repr(sorted(set(expected)-files)))
    require(dirs==expected_dirs,'unmanifested or missing input directories')
    return data,metadata

def write_new(path,data):
    fd=os.open(str(path),os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0),0o600)
    try:
        with os.fdopen(fd,'wb',closefd=False) as stream: stream.write(data);stream.flush()
    finally: os.close(fd)

def copy_snapshot(destination,files):
    destination.mkdir(mode=0o700)
    for name,data in sorted(files.items()):
        p=destination/name;p.parent.mkdir(parents=True,exist_ok=True)
        write_new(p,data);p.chmod(0o444)
    for base,dirs,names in os.walk(destination,topdown=False): Path(base).chmod(0o555)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',required=True,help='absolute frozen science directory')
    parser.add_argument('--audit',required=True,help='absolute frozen independent-audit directory')
    parser.add_argument('--output',required=True,help='absolute NEW external output directory; its parent must exist')
    args=parser.parse_args()
    packet=checked_path(args.packet,True);audit=checked_path(args.audit,True);output=checked_path(args.output,False)
    require(not below(packet,audit) and not below(audit,packet),'science/audit inputs must be disjoint')
    require(not below(output,packet) and not below(output,audit),'output must be external to both inputs')
    require(not below(packet,output) and not below(audit,output),'output may not contain an input')
    audit_manifest,_=read_regular(audit/'audit-manifest.json')
    require(sha(audit_manifest)==AUDIT_MANIFEST_SHA256,'audit manifest pin mismatch')
    am=parse(audit_manifest)
    science_manifest,_=read_regular(packet/'evidence/frozen-manifest.json')
    require(sha(science_manifest)==SCIENCE_MANIFEST_SHA256==am['author_manifest_sha256'],'science manifest pin mismatch')
    sm=parse(science_manifest)
    require(sm['files']==am['author_files'],'manifest inventories disagree')
    science_inventory=inventory(sm['files'],'evidence/frozen-manifest.json',science_manifest)
    audit_inventory=inventory(am['independent_files'],'audit-manifest.json',audit_manifest)
    science_bytes,science_metadata=read_tree(packet,science_inventory)
    audit_bytes,audit_metadata=read_tree(audit,audit_inventory)
    # Preflight completes before any output creation. Atomic exclusive mkdir rejects reuse.
    output.mkdir(mode=0o700)
    snapshot=output/'packet_snapshot';copy_snapshot(snapshot,science_bytes)
    results={}
    executable=str(Path(sys.executable).resolve())
    for mode,flags in [('normal',[]),('optimized',['-O'])]:
        run=output/mode;run.mkdir(mode=0o700)
        for name in ['check_source.py','check_interfaces.py']:
            write_new(run/name,audit_bytes[name]);(run/name).chmod(0o444)
        for script,label in [('check_source.py','source'),('check_interfaces.py','interface')]:
            proc=subprocess.run([executable,'-I','-S',*flags,str(run/script),str(snapshot)],cwd=run,
                                stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                                env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},timeout=300,check=False)
            write_new(run/(label+'.stdout.json'),proc.stdout)
            write_new(run/(label+'.stderr.txt'),proc.stderr)
            require(proc.returncode==0,'independent checker failed: '+mode+'/'+script)
            require(proc.stderr==b'','independent checker produced stderr: '+mode+'/'+script)
        results[mode]={}
        for name in RECEIPT_NAMES:
            data,_=read_regular(run/name)
            require(data==audit_bytes[name],'replay receipt mismatch: '+mode+'/'+name)
            require(parse(data)['status']=='PASS','replay receipt did not pass')
            results[mode][name]=sha(data)
    require(results['normal']==results['optimized'],'normal/optimized receipt mismatch')
    # Check snapshots and both original trees after all subprocesses. No input writes occur.
    snapshot_bytes,_=read_tree(snapshot,science_inventory)
    require(snapshot_bytes==science_bytes,'snapshot preservation failure')
    final_science,final_sm=read_tree(packet,science_inventory)
    final_audit,final_am=read_tree(audit,audit_inventory)
    require(final_science==science_bytes and final_audit==audit_bytes,'input byte preservation failure')
    require(final_sm==science_metadata and final_am==audit_metadata,'input metadata preservation failure')
    result={'schema':'chronological-matrix-portable-replay-v1','status':'PASS',
            'science_manifest_sha256':SCIENCE_MANIFEST_SHA256,'audit_manifest_sha256':AUDIT_MANIFEST_SHA256,
            'receipt_sha256':results['normal'],'normal_and_optimized_receipts_identical':True,
            'science_files_verified':len(science_inventory),'audit_files_verified':len(audit_inventory),
            'input_bytes_modes_mtimes_preserved':True,'readonly_packet_snapshot_preserved':True,
            'executed_only_pinned_independent_checkers':True,'author_or_upstream_code_executed':False,
            'saved_accepting_schedules_executed':False}
    receipt_bytes=encoded(result)
    emitted=[]
    for p in sorted(output.rglob('*')):
        require(not p.is_symlink(),'output symlink detected')
        if p.is_file():
            data,_=read_regular(p)
            emitted.append({'path':p.relative_to(output).as_posix(),'bytes':len(data),'sha256':sha(data)})
    emitted.append({'path':'replay-receipt.json','bytes':len(receipt_bytes),'sha256':sha(receipt_bytes)})
    emitted.sort(key=lambda item:item['path'])
    write_new(output/'replay-manifest.json',encoded({'schema':'portable-replay-output-manifest-v1','files':emitted}))
    # Success marker is published last; failed runs retain only partial diagnostic output.
    write_new(output/'replay-receipt.json',receipt_bytes)
    sys.stdout.buffer.write(receipt_bytes)

if __name__=='__main__':
    try: main()
    except (ReplayError,OSError,ValueError,KeyError,TypeError,subprocess.TimeoutExpired) as exc:
        print('REPLAY FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
