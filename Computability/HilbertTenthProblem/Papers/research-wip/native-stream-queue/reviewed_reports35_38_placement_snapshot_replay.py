#!/usr/bin/env python3
"""Replay exact Reports35-38 archives and original placement snapshots.
Frozen JSON inventory and historical/current member bytes are inert data.
"""
import argparse
from collections import Counter
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import zipfile

REVISION = '7f9672c599194e150dee64ebaa0b19f0e035ba15'
PLACEMENTS = ['216bd81e116297214f443afddc2fc6252a7767a6',
              'a51a439cdcb43701241c83fdf8d185630df0b18d']
INVENTORY_SHA256 = '73f427c5bd74ea00e1aea1af40b550404346eecb08adf52606094cee471c623c'
GUARD_PREDECESSOR_SHA256 = '09af8babf9c1a68b33b42374c475b473939613a5ccbc01f85ef2453ab9554d69'

def require(ok,message):
    if not ok: raise ValueError(message)
def digest(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def git(repo,*args):
    p=subprocess.run(['git','--no-pager','-C',str(repo),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    require(p.returncode==0,'Git read failed: '+p.stderr.decode(errors='replace').strip())
    return p.stdout

def inside(p,parent): return p==parent or parent in p.parents

def normalized(path):
    require('..' not in path.parts,'parent traversal is not an output path')
    return Path(os.path.abspath(path))

# Every write is relative to verified open directory descriptors. No output
# ancestor or leaf symlink is followed; files are created exclusively and never
# overwritten. These are filesystem guards, not a promise against arbitrary
# concurrent hostile directory renaming or storage failure.
def parent_fd(path,create=False):
    fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY)
    try:
        for part in path.parts[1:-1]:
            try:
                nxt=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            except FileNotFoundError:
                if not create:
                    os.close(fd);return None
                try: os.mkdir(part,mode=0o700,dir_fd=fd)
                except FileExistsError: pass
                nxt=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            os.close(fd);fd=nxt
        return fd
    except BaseException:
        os.close(fd);raise

def regular_bytes(fd,name):
    leaf=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=fd)
    try:
        require(stat.S_ISREG(os.fstat(leaf).st_mode),'output is not a regular file')
        with os.fdopen(leaf,'rb',closefd=False) as stream: return stream.read()
    finally: os.close(leaf)

def preflight(path,expected,protected):
    require(path.name not in ('','/'),'file output must have a leaf')
    for directory in protected:
        require(not inside(path,directory),'output lies inside protected repository storage')
    fd=parent_fd(path)
    if fd is None:return
    try:
        try: old=regular_bytes(fd,path.name)
        except FileNotFoundError:return
        require(old==expected,'refuse differing existing output: '+str(path))
    finally:os.close(fd)

def write_same_or_new(path,data,protected):
    preflight(path,data,protected)
    fd=parent_fd(path,True)
    try:
        try:
            leaf=os.open(path.name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600,dir_fd=fd)
        except FileExistsError:
            require(regular_bytes(fd,path.name)==data,'existing output changed')
        else:
            with os.fdopen(leaf,'wb') as stream:stream.write(data)
        require(regular_bytes(fd,path.name)==data,'written bytes differ')
    finally:os.close(fd)

def prepare(repo_arg,cache_arg,inventory_arg):
    inventory_bytes=inventory_arg.read_bytes()
    require(digest(inventory_bytes)==INVENTORY_SHA256,'frozen inventory JSON pin')
    inventory_data=json.loads(inventory_bytes)
    require(inventory_data['historical_revision']==REVISION and inventory_data['placement_commits']==PLACEMENTS,'exact inventory revision routing')
    inventory=inventory_data['archives']
    repo=repo_arg.resolve(strict=True)
    require(repo.is_dir(),'repository directory')
    actual=Path(git(repo,'rev-parse','--show-toplevel').decode().strip()).resolve(strict=True)
    require(actual==repo,'--repo-root must be actual worktree root')
    require(git(repo,'rev-parse','--verify',REVISION+'^{commit}').decode().strip()==REVISION,'exact historical revision')
    for placement in PLACEMENTS:
        require(git(repo,'rev-parse','--verify',placement+'^{commit}').decode().strip()==placement,'exact placement revision')
    protected=[repo]
    for flag in ('--git-dir','--git-common-dir'):
        p=Path(git(repo,'rev-parse','--path-format=absolute',flag).decode().strip()).resolve(strict=True)
        protected.append(p)
    cache=normalized(cache_arg)
    for p in protected:
        require(not inside(cache,p) and not inside(p,cache),'cache intersects protected repository storage')
    # Probe an otherwise unused child to validate the complete cache ancestor
    # chain without creating directories or requiring the cache to exist.
    fd=parent_fd(cache/'__path_probe__')
    if fd is not None:os.close(fd)
    require(len(inventory)==4 and len({r['name'] for r in inventory})==4,'fixed four-archive scope')
    work=[];records=[];member_count=0;relations=Counter();current_paths=set();snapshot_paths=set()
    for record in inventory:
        name=record['name'];require(Path(name).name==name and name.endswith('.zip'),'fixed archive basename')
        raw=git(repo,'cat-file','blob',REVISION+':docs/incoming/'+name)
        require(len(raw)==record['bytes'] and digest(raw)==record['sha256'],'exact archive size/SHA256')
        oid=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(oid==record['git_blob_sha1'],'Git blob SHA1')
        copied=dict(record);copied['members']=[]
        placement=PLACEMENTS[0] if record['report'] in (35,36) else PLACEMENTS[1]
        require(record['report'] in (35,36,37,38),'fixed report identifier')
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            require(len(z.namelist())==len(set(z.namelist())),'unique ZIP members')
            for m in record['members']:
                b=z.read(m['member'])
                require(len(b)==m['bytes'] and digest(b)==m['sha256'],'selected member size/SHA256')
                item={k:m[k] for k in ('member','bytes','sha256')}
                if m['relation']=='byte_identical_new_placement':
                    relative=Path(m['current_path'])
                    require(not relative.is_absolute() and '..' not in relative.parts,'fixed placement path')
                    placed=git(repo,'cat-file','blob',placement+':'+str(relative))
                    require(placed==b,'placement/member full-byte identity: '+str(relative))
                    item.update(relation='byte_identical_placement_snapshot',placement_commit=placement,placement_path=str(relative))
                    snapshot_paths.add((placement,str(relative)))
                elif m['relation']=='byte_identical_existing_frozen_source':
                    relative=Path(m['current_path'])
                    require(not relative.is_absolute() and '..' not in relative.parts,'fixed current source path')
                    require((repo/relative).read_bytes()==b,'current/member full-byte identity: '+str(relative))
                    item.update(relation='byte_identical_existing_frozen_source',current_path=str(relative))
                    current_paths.add(str(relative))
                else:
                    require(m['relation']=='archive_only_context' and m['current_path'] is None,'archive-only scope')
                    item['relation']='archive_only_context'
                copied['members'].append(item);relations[item['relation']]+=1;member_count+=1
        dest=cache/'docs/incoming'/name
        preflight(dest,raw,protected);work.append((dest,raw));records.append(copied)
    require(member_count==24 and len(snapshot_paths)==16 and len(current_paths)==5,'selected snapshot/current-source inventory')
    require(dict(relations)=={'byte_identical_placement_snapshot':17,'archive_only_context':2,'byte_identical_existing_frozen_source':5},'exact relocation scope')
    receipt=dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),historical_revision=REVISION,
                 inventory_sha256=INVENTORY_SHA256,guard_predecessor_sha256=GUARD_PREDECESSOR_SHA256,placement_commits=PLACEMENTS,archives=records,archive_count=4,archive_bytes=sum(r['bytes'] for r in records),
                 authenticated_members=member_count,member_relations=dict(relations),distinct_placement_snapshots=len(snapshot_paths),distinct_current_files=len(current_paths),
                 verification=dict(archive_extraction=False,archive_execution=False,repository_writes=False,
                                   source_bridge_created=False,overwrite_differing=False,exclusive_new_files=True,
                                   no_output_symlink_following=True),
                 scope='Exact original archive and historical placement-snapshot compatibility. Only five existing frozen source paths are checked in the current worktree; current published report articles and READMEs are not pinned. No scientific theorem or archived verifier is rerun.')
    return protected,work,receipt

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root',type=Path,required=True);p.add_argument('--output-root',type=Path,required=True)
    p.add_argument('--inventory',type=Path,default=Path(__file__).with_name('reviewed_reports35_38_archive_replay.json'))
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();protected,work,r=prepare(a.repo_root,a.output_root,a.inventory)
    encoded=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode()
    if a.expect:require(exact(r,json.loads(a.expect.read_text())),'saved exact typed receipt')
    receipt_path=normalized(a.output) if a.output else None
    if receipt_path:
        require(receipt_path not in {p for p,b in work},'receipt cannot replace an archive')
        preflight(receipt_path,encoded,protected)
    for path,data in work:write_same_or_new(path,data,protected)
    if receipt_path:write_same_or_new(receipt_path,encoded,protected)
    print(json.dumps({k:r[k] for k in ('status','archive_count','archive_bytes','authenticated_members','distinct_placement_snapshots','distinct_current_files')},sort_keys=True))
if __name__=='__main__':main()
