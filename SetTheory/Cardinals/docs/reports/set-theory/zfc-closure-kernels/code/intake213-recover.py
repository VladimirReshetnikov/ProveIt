#!/usr/bin/env python3
# SPDX-License-Identifier: MIT-0
"""Own exact supplemental213 recovery; all delivered contents are inert data."""
import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

HOST = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
ARRIVAL = '4b16429bf6d2557b7b168792efa5f487443d6e77'
EXPECTED_ARCHIVES = [
  {
    "manuscript": 1,
    "source": 180,
    "archive_path": "docs/incoming/K215_Further_Interface_Simplification_2026-10-21.zip",
    "archive_sha256": "bb77c00241a46a409f9cfb76fcd500d6b8d7a9178a066de997f5bf428b9669b7",
    "archive_bytes": 206007
  },
  {
    "manuscript": 2,
    "source": 181,
    "archive_path": "docs/incoming/K215_Proof_Contracts_2026-10-21.zip",
    "archive_sha256": "05e057ab70390a7a8b90d1ac815ebe112b6f85090007525b44baee68ba43e5f1",
    "archive_bytes": 664963
  },
  {
    "manuscript": 3,
    "source": 182,
    "archive_path": "docs/incoming/K215_Proof_Simplification_2026-10-21 (1).zip",
    "archive_sha256": "b7b8e649d67fc4b897687ecb9288df39cfff78f1d8ebdf5e19e6d09a25e0ba38",
    "archive_bytes": 433721
  },
  {
    "manuscript": 4,
    "source": 183,
    "archive_path": "docs/incoming/K215_Proof_Simplification_2026-10-21.zip",
    "archive_sha256": "32c128cc37784ef8f86accad9ddee163cbe700e194f6c32268ced1f918c6a3ae",
    "archive_bytes": 678723
  },
  {
    "manuscript": 5,
    "source": 184,
    "archive_path": "docs/incoming/K215_Semantic_Proof_Simplification_2026-10-21.zip",
    "archive_sha256": "37e94119282fe0d2a83bee577d14ba90842e3417e113142e4a2f88b607356e3e",
    "archive_bytes": 606553
  },
  {
    "manuscript": 6,
    "source": 185,
    "archive_path": "docs/incoming/K215_Shared_Proof_Core_2026-10-21.zip",
    "archive_sha256": "e8aff5052f8734b7dc90c8754171f1d09e5f3f11ec4186544eb154ea2e909081",
    "archive_bytes": 528144
  },
  {
    "manuscript": 7,
    "source": 186,
    "archive_path": "docs/incoming/Sharing_Semantic_Interfaces_Rocq_and_Lean_2026-10-21.zip",
    "archive_sha256": "6fa7c6648c3d6e39e6bd53223cd4affe972af381ef316f6da5f9f815213afda0",
    "archive_bytes": 590259
  },
  {
    "manuscript": 8,
    "source": 187,
    "archive_path": "docs/incoming/k215-proof-simplification-2026-10-21.zip",
    "archive_sha256": "c47f6c0ab71d92bb68af29841b13f352fa0782349169de0017f2e5221ca6aadd",
    "archive_bytes": 385708
  }
]
COUNTS = {'git':676,'arrival_member':69,'delivery_member':42,'placed':1}

def require(ok, message):
    if not ok: raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    require(isinstance(name,str) and bool(name), 'Empty/non-string path')
    p=PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in name
            and '\n' not in name and '\r' not in name
            and not re.match(r'^[A-Za-z]:',name), 'Unsafe path: '+name)
    return name

class Git:
    def __init__(self, repo):
        self.proc=subprocess.Popen(['git','-C',str(repo),'cat-file','--batch'],
            stdin=subprocess.PIPE,stdout=subprocess.PIPE)
        self.cache={}

    def read(self, commit, path):
        require(re.fullmatch('[0-9a-f]{40}',commit) is not None,'Non-immutable Git reference')
        query=commit+':'+safe(path)
        if query in self.cache: return self.cache[query]
        self.proc.stdin.write((query+'\n').encode()); self.proc.stdin.flush()
        fields=self.proc.stdout.readline().decode().strip().split()
        require(len(fields)==3 and fields[1]=='blob','Missing Git blob: '+query)
        n=int(fields[2]);data=self.proc.stdout.read(n)
        require(len(data)==n and self.proc.stdout.read(1)==b'\n','Truncated Git response')
        self.cache[query]=data
        return data

    def close(self):
        self.proc.stdin.close();self.proc.stdout.close()
        require(self.proc.wait(timeout=10)==0,'Git reader failed')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=Path.cwd())
    ap.add_argument('--map',type=Path)
    mode=ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--verify-only',action='store_true')
    mode.add_argument('--out',type=Path)
    ap.add_argument('--result',type=Path)
    args=ap.parse_args(); repo=args.repo.resolve()
    path=args.map or repo/HOST/'data/intake213-placement.json'
    raw=path.read_bytes();m=json.loads(raw)
    require((m['batch'],m['sources'],m['member_count'],m['member_bytes'])==
            (213,list(range(180,188)),788,10266210),'Wrong batch/source/member boundary')
    require(m['arrival_commit']==ARRIVAL,'Wrong arrival commit')
    identities=[{k:a[k] for k in ['manuscript','source','archive_path','archive_sha256','archive_bytes']}
                for a in m['archives']]
    require(identities==EXPECTED_ARCHIVES,'Wrong immutable archive identities')
    require(m['counts']==COUNTS,'Wrong route counts')
    require([r['manuscript'] for r in m['members']]==sorted(r['manuscript'] for r in m['members']),
            'Member archives reordered')
    g=Git(repo); recovered={}; checked=0; total=0
    try:
        for a in EXPECTED_ARCHIVES:
            archive=g.read(ARRIVAL,a['archive_path'])
            require(len(archive)==a['archive_bytes'] and sha(archive)==a['archive_sha256'],
                    'Arrival bytes changed')
            with zipfile.ZipFile(io.BytesIO(archive)) as z:
                infos=z.infolist();names=[safe(i.filename) for i in infos]
                require(len(names)==len(set(names)),'Duplicate archive name')
                require(all(not i.is_dir() and not(i.flag_bits&1) and
                    ((i.external_attr>>16)&0o170000)!=0o120000 for i in infos),
                    'Unsupported archive member')
                rows=[r for r in m['members'] if r['manuscript']==a['manuscript']]
                require([r['member'] for r in rows]==names,'Missing/reordered map member')
                for r in rows:
                    require(r['source']==a['source'],'Wrong source number')
                    name=r['member'];route=r['route']
                    if route=='git': data=g.read(r['commit'],r['path'])
                    elif route=='placed':
                        f=repo/safe(r['path'])
                        require(f.is_file() and not f.is_symlink(),'Missing placed member')
                        data=f.read_bytes()
                    elif route=='arrival_member': data=z.read(name)
                    elif route=='delivery_member':
                        key=(r['target_manuscript'],r['target_member'])
                        require(key in recovered,'Unknown/forward delivery alias')
                        data=recovered[key]
                    else: raise ValueError('Unknown route: '+route)
                    require(len(data)==r['bytes'] and sha(data)==r['sha256'],
                            'Member bytes changed: '+name)
                    require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==
                            r['git_blob'],'Wrong raw Git identity: '+name)
                    require(data==z.read(name),'Recovery differs from arrival: '+name)
                    recovered[(a['manuscript'],name)]=data;checked+=1;total+=len(data)
        require((checked,total)==(788,10266210),'Total recovery boundary failed')
        require(dict(Counter(r['route'] for r in m['members']))==COUNTS,'Route census mismatch')
        if args.out:
            require(not args.out.exists(),'Output directory already exists')
            for (num,name),data in recovered.items():
                f=args.out/f'{num:02d}'/name;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
    finally:
        g.close()
    result={'status':'PASS_EXACT_788_MEMBER_RECOVERY','batch':213,'sources':list(range(180,188)),
        'map_sha256':sha(raw),'helper_sha256':sha(Path(__file__).read_bytes()),
        'members':checked,'bytes':total,'routes':COUNTS,
        'mode':'reconstruct' if args.out else 'verify_only','output':str(args.out) if args.out else None,
        'supplied_code_or_compiler_executed':False,'checksum_manifest_contents_checked':False}
    if args.result: args.result.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
