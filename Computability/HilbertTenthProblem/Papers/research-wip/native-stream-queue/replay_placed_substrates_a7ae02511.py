#!/usr/bin/env python3
"""Authenticate six placed packets and restore their original package layouts.

All seven removed archives are authenticated from the pinned parent commit.
The older signal package is superseded by its corrected revision and is not
staged over that shared root. No recovered source is executed or patched.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tempfile
import zipfile

COMMIT='a7ae02511c5584086ef9152f92d59ba77efa6148'
PARENT='38edfb31e40af6aa99c9d552a47e111d3f3eb8da'
INVENTORY_SHA='cec197a4c1367d9dcd671ba85fa242fbdaba5445251794535f0333c2228687cf'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def safe(name):
    p=PurePosixPath(name)
    need(type(name) is str and bool(p.parts) and not p.is_absolute() and '..' not in p.parts and '\\' not in name,'Unsafe relative path')
    return Path(*p.parts)
def git(repo,*args):return subprocess.check_output(['git',*args],cwd=repo,timeout=120)
def inventory(path):
    raw=Path(path).read_bytes();need(sha(raw)==INVENTORY_SHA,'Inventory pin differs');data=json.loads(raw)
    need(data['placement_commit']==COMMIT and data['placement_parent']==PARENT and not data['unmatched_files'],'Wrong placement inventory')
    return data

def stage(repo,dest,inventory_path):
    repo,dest=Path(repo).resolve(),Path(dest);data=inventory(inventory_path)
    need(not dest.exists(),'Destination must not exist')
    current={};qualified_targets={};newline_records=[]
    for row in data['matched_files']:
        path=safe(row['path']);content=(repo/path).read_bytes()
        need(sha(content)==row['sha256'] and len(content)==row['bytes'],'Placed source differs: '+row['path'])
        need(path.name.startswith(row['package_prefix']),'Incorrect filename package prefix')
        archive=data['package_prefix_bindings'][row['package_prefix']]
        need(row['source_matches'] and all(m['archive']==archive for m in row['source_matches']),'Cross-package provenance mapping')
        current[row['path']]=content
        for match in row['source_matches']:
            target=(match['archive'],match['member']);need(target not in qualified_targets,'One original member assigned multiple placed files')
            qualified_targets[target]=row['path']
        if path.suffix=='.csv':
            newline_records.append(dict(path=row['path'],CRLF=content.count(b'\r\n'),bare_LF=content.count(b'\n')-content.count(b'\r\n')))
    need(git(repo,'rev-parse',COMMIT+'^').decode().strip()==PARENT,'Placement parent drift')
    attribute_records=[]
    for record in data['modified_nonarchive_files']:
        path=record['path'];before=git(repo,'show',PARENT+':'+path);after=git(repo,'show',COMMIT+':'+path)
        need(sha(before)==record['before_sha256'] and sha(after)==record['after_sha256'],'Pinned metadata revision differs')
        need(after==before+('\n'.join(record['added_lines'])+'\n').encode(),'Unexpected metadata modification')
        current_attributes=(repo/safe(path)).read_text()
        need(all(line in current_attributes.splitlines() for line in record['added_lines']),'Required current CRLF attributes absent')
        attribute_records.append({k:v for k,v in record.items() if k!='patch'})
    archives={};all_members={}
    for record in data['archives']:
        name=record['path'];content=git(repo,'show',PARENT+':'+name)
        need(sha(content)==record['sha256'] and len(content)==record['bytes'],'Pinned original ZIP differs: '+name)
        expected={m['member']:m for m in record['members']};need(len(expected)==len(record['members']),'Duplicate member inventory')
        members={}
        with zipfile.ZipFile(io.BytesIO(content)) as z:
            entries=z.infolist();need(len(entries)==len({e.filename for e in entries}),'Duplicate ZIP entry')
            for e in entries:
                p=safe(e.filename);need((e.external_attr>>16)&0o170000!=0o120000,'ZIP symlink')
                if e.is_dir():continue
                value=z.read(e);need(e.filename in expected and sha(value)==expected[e.filename]['sha256'] and len(value)==expected[e.filename]['bytes'],'Member bytes differ')
                members[e.filename]=value
        need(set(members)==set(expected),'Full ZIP member manifest differs');all_members[name]=members
        archives[name]=dict(sha256=record['sha256'],members=len(members),staged=record['staged'])
    # Validate every mapping before creating any destination files.
    staged={};roots={}
    for name in data['staged_archives']:
        need(archives[name]['staged'],'Archive staging classification differs')
        for member,content in all_members[name].items():
            need(member not in staged,'Cross-package extraction collision');staged[member]=content
        roots[name]=sorted({PurePosixPath(m).parts[0] for m in all_members[name]})
    for (name,member),path in qualified_targets.items():
        need(name in data['staged_archives'] and all_members[name][member]==current[path],'Qualified placement is not identical to original')
        staged[member]=current[path]
    need(len(staged)==data['counts']['staged_archive_file_members']==334,'Restored member count mismatch')
    need(len(qualified_targets)==252 and len(current)==246,'Placement target count mismatch')
    dest.mkdir(parents=True,exist_ok=False)
    for member,content in staged.items():
        target=dest/safe(member);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(content)
    # Full per-root manifests, including all omitted/redundant original members.
    root_records=[]
    for name in data['staged_archives']:
        expected=all_members[name];root=roots[name]
        need(len(root)==1,'Expected one original root per active package')
        actual={str(p.relative_to(dest)):p.read_bytes() for p in (dest/root[0]).rglob('*') if p.is_file()}
        need(set(actual)==set(expected) and all(actual[m]==content for m,content in expected.items()),'Restored complete package manifest differs')
        full_digest=sha(json.dumps({m:sha(v) for m,v in sorted(actual.items())},sort_keys=True,separators=(',',':')).encode())
        n=sum(a==name for a,m in qualified_targets)
        root_records.append(dict(archive=name,root=root[0],members=len(actual),from_qualified_placement=n,from_git_only=len(actual)-n,full_member_manifest_sha256=full_digest))
    return dict(status='PASS_EXACT_PLACEMENT_RESTORATION',placement_commit=COMMIT,placement_parent=PARENT,inventory_sha256=INVENTORY_SHA,counts=data['counts'],archive_authentication=archives,restored_packages=root_records,same_package_aliases=data['same_package_aliases'],superseded_archives=data['superseded_archives'],nonarchive_metadata=attribute_records,csv_newlines=newline_records,scope='All246 added files authenticated against intended package members; six exact original layouts restored and all334 file bytes compared. Seven removed archives authenticated, older signal revision not overlaid. No source execution, source repair, author-suite replay or new mathematical audit.')

def verify(repo,inventory_path=None):
    path=Path(inventory_path) if inventory_path is not None else Path(__file__).with_name('placement_a7ae02511_inventory.json')
    with tempfile.TemporaryDirectory(prefix='placement-a7ae02511-') as tmp:return stage(repo,Path(tmp)/'packages',path)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--destination',type=Path);p.add_argument('--inventory',type=Path,default=Path(__file__).with_name('placement_a7ae02511_inventory.json'));p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
    out=stage(a.repo,a.destination,a.inventory) if a.destination is not None else verify(a.repo,a.inventory)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Saved restoration receipt differs')
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
