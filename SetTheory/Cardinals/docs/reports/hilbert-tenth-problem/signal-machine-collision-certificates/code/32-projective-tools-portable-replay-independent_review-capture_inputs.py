#!/usr/bin/env python3
"""Fresh reviewer metadata/content snapshotter; imports no packet code."""
from pathlib import Path
import hashlib,json,os,stat,sys
ROOTS={'science':'/workspace/shared/projective-signal-shears62-20261004','audit':'/workspace/shared/audit-projective-signal-shears62-20261004'}
rows={}
for label,raw in ROOTS.items():
    root=Path(raw); entries=[]
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat(); row={'path':'.' if p==root else p.relative_to(root).as_posix(),'mode':oct(stat.S_IMODE(s.st_mode)),'mtime_ns':s.st_mtime_ns,'size':s.st_size,'kind':'regular' if stat.S_ISREG(s.st_mode) else 'directory' if stat.S_ISDIR(s.st_mode) else 'other','inode':s.st_ino,'device':s.st_dev,'nlink':s.st_nlink}
        if stat.S_ISREG(s.st_mode): row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(row)
    rows[label]=entries
Path(sys.argv[1]).write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
