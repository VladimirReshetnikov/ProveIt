#!/usr/bin/env python3
"""Manifest, byte verification and deterministic ZIP for Report65; no scientific execution."""
import argparse,hashlib,json,stat,struct,zipfile
from pathlib import Path,PurePosixPath
PREFIX='Report65/'
STAMP=(2026,10,4,0,0,0)
def require(v,s):
    if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def encoded(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def rootpath(p):
    p=p.absolute();require(p.resolve(strict=True)==p,'Root contains symlink or noncanonical component');require(p.is_dir(),'Root is not a directory');return p
def safe(s):
    p=PurePosixPath(s);return bool(s) and not p.is_absolute() and str(p)==s and all(t not in ('','.', '..') for t in p.parts) and '\\' not in s
def inventory(root):
    files={};dirs=[]
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix();require(safe(rel),'Unsafe relative path')
        require(not p.is_symlink(),'Symlink rejected: '+rel)
        st=p.stat();require(stat.S_ISREG(st.st_mode) or stat.S_ISDIR(st.st_mode),'Special file rejected: '+rel)
        if p.is_dir():dirs.append(rel)
        elif rel!='MANIFEST.json':files[rel]={'bytes':st.st_size,'sha256':sha(p.read_bytes()),'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns}
    return files,dirs
def check_inputs(root):
    p=root/'INPUT_PINS.json';require(p.is_file(),'Missing INPUT_PINS')
    pins=json.loads(p.read_text());seen=set()
    for row in pins:
        rel=row['copy'];require(safe(rel) and rel not in seen,'Invalid input pin path');seen.add(rel)
        q=root/rel;require(q.is_file() and not q.is_symlink(),'Missing pinned input '+rel)
        require(sha(q.read_bytes())==row['sha256'] and q.stat().st_size==row['bytes'],'Pinned input mismatch '+rel)
    return len(pins)
def verify(root,pin,metadata=False):
    p=root/'MANIFEST.json';require(p.is_file() and not p.is_symlink(),'Missing manifest')
    require(stat.S_IMODE(p.stat().st_mode)==0o644,'Manifest mode must be 0644')
    data=p.read_bytes();require(sha(data)==pin,'Manifest digest mismatch');m=json.loads(data)
    require(m.get('schema')=='report65-release-v1','Wrong manifest schema')
    files,dirs=inventory(root);require(set(files)==set(m['files']),'File set differs');require(dirs==m['directories'],'Directory set differs')
    for rel,row in files.items():
        old=m['files'][rel]
        for key in ('bytes','sha256','mode')+ (('mtime_ns',) if metadata else ()):
            require(row[key]==old[key],'File mismatch '+rel+' '+key)
    check_inputs(root);return m

def new_output(p,root):
    p=p.absolute();require(not p.exists() and not p.is_symlink(),'Output exists')
    require(p.parent.resolve(strict=True)==p.parent,'Output parent contains symlink')
    require(root!=p and root not in p.parents and p not in root.parents,'Output overlaps release');return p

def archive_check(path,pin):
    with zipfile.ZipFile(path,'r') as z:
        require(not z.comment,'Noncanonical archive comment')
        infos=z.infolist();names=[i.filename for i in infos]
        require(len(names)==len(set(names)),'Duplicate ZIP member')
        require(all(n.startswith(PREFIX) and safe(n[len(PREFIX):]) for n in names),'Unsafe ZIP member')
        require(PREFIX+'MANIFEST.json' in names,'Missing archive manifest')
        data=z.read(PREFIX+'MANIFEST.json');require(sha(data)==pin,'Archive manifest digest mismatch');m=json.loads(data)
        require(m.get('schema')=='report65-release-v1','Wrong archive schema')
        require(set(names)=={PREFIX+x for x in m['files']}|{PREFIX+'MANIFEST.json'},'Archive member set differs')
        for info in infos:
            require(not info.extra and not info.comment,'Noncanonical ZIP metadata')
            with path.open('rb') as raw:
                raw.seek(info.header_offset);header=raw.read(30)
            require(len(header)==30,'Truncated local ZIP header')
            fields=struct.unpack('<IHHHHHIIIHH',header)
            require(fields[0]==0x04034b50 and fields[-1]==0,'Noncanonical local ZIP extra field')
            require(not info.flag_bits & 1,'Encrypted member rejected');require(info.date_time==STAMP,'Unexpected member timestamp')
            mode=info.external_attr>>16;require(stat.S_ISREG(mode),'Nonregular ZIP member')
            if info.filename==PREFIX+'MANIFEST.json':
                require(stat.S_IMODE(mode)==0o644,'Archive manifest mode mismatch')
                continue
            row=m['files'][info.filename[len(PREFIX):]];b=z.read(info)
            require(len(b)==row['bytes'] and sha(b)==row['sha256'],'Archive content mismatch')
            require(stat.S_IMODE(mode)==row['mode'],'Archive mode mismatch')
        return {'status':'PASS','archive_sha256':sha(path.read_bytes()),'manifest_sha256':pin,'members':len(names)}

def main():
    ap=argparse.ArgumentParser(description=__doc__);sub=ap.add_subparsers(dest='command',required=True)
    for cmd in ('seal','verify','archive'):
        p=sub.add_parser(cmd);p.add_argument('--root',type=Path,required=True)
        if cmd!='seal':p.add_argument('--manifest-sha256',required=True)
        if cmd=='verify':p.add_argument('--metadata',action='store_true');p.add_argument('--origins',action='store_true')
        if cmd=='archive':p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('archive-check');p.add_argument('--archive',type=Path,required=True);p.add_argument('--manifest-sha256',required=True)
    a=ap.parse_args()
    if a.command=='archive-check':print(json.dumps(archive_check(a.archive,a.manifest_sha256),indent=2));return
    root=rootpath(a.root)
    if a.command=='seal':
        require(not (root/'MANIFEST.json').exists(),'Refusing to replace manifest');n=check_inputs(root)
        files,dirs=inventory(root);require('Report65.pdf' in files and 'Report65.tex' in files,'Missing deliverables')
        require(all(any(f.startswith(d+'/') for f in files) for d in dirs),'Empty directories cannot be archived')
        m={'schema':'report65-release-v1','date':'2026-10-04','scientific_execution':False,'files':files,'directories':dirs,'inert_input_count':n}
        with (root/'MANIFEST.json').open('xb') as f:f.write(encoded(m))
        (root/'MANIFEST.json').chmod(0o644)
        print(json.dumps({'status':'SEALED','manifest_sha256':sha(encoded(m)),'files':len(files)},indent=2));return
    m=verify(root,a.manifest_sha256,getattr(a,'metadata',False))
    if a.command=='verify':
        if a.origins:
            for row in json.loads((root/'INPUT_PINS.json').read_text()):
                p=Path(row['origin']);require(p.is_file() and not p.is_symlink(),'Missing original')
                st=p.stat();require(sha(p.read_bytes())==row['sha256'] and st.st_size==row['bytes'] and oct(stat.S_IMODE(st.st_mode))==row['mode'] and st.st_mtime_ns==row['mtime_ns'] and st.st_ctime_ns==row['ctime_ns'],'Original changed '+str(p))
        print(json.dumps({'status':'PASS','manifest_sha256':a.manifest_sha256,'files':len(m['files']),'origins_checked':a.origins},indent=2));return
    before=inventory(root)
    out=new_output(a.output,root)
    with zipfile.ZipFile(out,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for rel in sorted([*m['files'],'MANIFEST.json']):
            info=zipfile.ZipInfo(PREFIX+rel,STAMP);info.create_system=3;info.compress_type=zipfile.ZIP_DEFLATED
            mode=0o644 if rel=='MANIFEST.json' else m['files'][rel]['mode'];info.external_attr=(stat.S_IFREG|mode)<<16
            info.flag_bits=0;z.writestr(info,(root/rel).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    verify(root,a.manifest_sha256,False)
    require(before==inventory(root),'Source changed during archive creation')
    print(json.dumps(archive_check(out,a.manifest_sha256),indent=2))
if __name__=='__main__':main()
