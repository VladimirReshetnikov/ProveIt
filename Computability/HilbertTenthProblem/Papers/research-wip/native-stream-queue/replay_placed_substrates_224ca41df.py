#!/usr/bin/env python3
"""Rehydrate byte-identical placed sources into original runnable package layouts.

Omitted source documents, manifests and regenerable fixtures come from Git.
Every placed file is authenticated, then overlaid from the current checkout.
This stages research artifacts only; it executes no recovered source.
"""
import argparse, hashlib, io, json
from pathlib import Path
import subprocess, zipfile

COMMIT='224ca41df204ab800fab13c70ceb63b12703a624'
INVENTORY_SHA='a6785bc7b58866712b543c8e0a72319ed9bb4aacf69c62f1ea881f90f443b41d'

def need(value,message):
    if not value:raise ValueError(message)

def sha(data):return hashlib.sha256(data).hexdigest()

def stage(repo,dest,inventory):
    raw=inventory.read_bytes();need(sha(raw)==INVENTORY_SHA,'inventory changed')
    data=json.loads(raw);need(data['placement_commit']==COMMIT and not data['unmatched_files'],'unmatched placement')
    current={}
    for row in data['matched_files']:
        p=Path(row['path']);need(not p.is_absolute() and '..' not in p.parts,'unsafe placed path')
        content=(repo/p).read_bytes();need(sha(content)==row['sha256'],'placed source differs: '+str(p));current[str(p)]=content
    archives={}
    for name in data['removed_archives']:
        content=subprocess.check_output(['git','show',COMMIT+'^:'+name],cwd=repo)
        expected={match['archive_sha256'] for row in data['matched_files'] for match in row['source_matches'] if match['archive']==name}
        need(expected=={sha(content)},'Git archive does not match pinned source');archives[name]=content
    dest.mkdir(parents=True,exist_ok=False);roots={};total=0
    for name,content in archives.items():
        with zipfile.ZipFile(io.BytesIO(content)) as z:
            entries=z.infolist();need(len(entries)==len({x.filename for x in entries}),'duplicate archive members')
            for entry in entries:
                p=Path(entry.filename);need(not p.is_absolute() and '..' not in p.parts and '\\' not in entry.filename and (entry.external_attr>>16)&0o170000!=0o120000,'unsafe archive member')
                if entry.is_dir():continue
                need(p.parts,'empty archive name');roots.setdefault(name,set()).add(p.parts[0]);target=dest/p
                need(not target.exists(),'cross-archive collision');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(entry));total+=1
    for row in data['matched_files']:
        for match in row['source_matches']:
            target=dest/match['member'];need(target.read_bytes()==current[row['path']],'placement is not byte-identical');target.write_bytes(current[row['path']])
    return dict(status='PASS',placement_commit=COMMIT,placed_files=len(current),archives=len(archives),restored_members=total,package_roots={name:sorted(root) for name,root in roots.items()},scope='Exact layout restoration; mathematical review and author suites are separate. Sources have not been patched or executed.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--destination',type=Path,required=True);p.add_argument('--inventory',type=Path,default=Path(__file__).with_name('placement_224ca41df_inventory.json'));p.add_argument('--output',type=Path);a=p.parse_args();r=stage(a.repo,a.destination,a.inventory)
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))
