#!/usr/bin/env python3
"""Fresh read-only metadata/hash inventory. Never executes input content."""
import argparse,hashlib,json,os,stat
from pathlib import Path

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def inventory(roots):
    result=[]
    for root in roots:
        p=Path(root).resolve()
        for q in [p]+sorted(p.rglob('*')) if p.is_dir() else [p]:
            s=q.lstat(); assert not q.is_symlink(),str(q)
            x={'path':str(q),'mode':s.st_mode,'size':s.st_size,'mtime_ns':s.st_mtime_ns,'is_dir':q.is_dir()}
            if q.is_file():x['sha256']=digest(q)
            result.append(x)
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--compare',type=Path)
    a=p.parse_args(); src=a.source.resolve(); assert src not in a.out.resolve().parents
    hist=json.loads((src/'evidence/source_before.json').read_text())
    paths={x['path'] for x in hist}
    roots=sorted(x for x in paths if str(Path(x).parent) not in paths)
    roots += [str(src),str(src)+'.zip']
    data=inventory(roots);a.out.write_text(json.dumps(data,indent=2)+'\n')
    if a.compare:assert data==json.loads(a.compare.read_text()),'current baseline changed'
    print(json.dumps({'entries':len(data),'roots':roots,'compare_equal':bool(a.compare),'sha256':digest(a.out)}))
