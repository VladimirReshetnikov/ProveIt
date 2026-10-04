"""Read-only byte/mode/mtime inventories; never imports source packets."""
from pathlib import Path
import hashlib, json, os, stat, sys
BASE=Path('/workspace/shared')
NAMES=['five-signal-planar-realization60-20261004','five-signal-planar-realization60-independent-review-20261004','planar-strict-kernel-classification-20261004','planar-strict-kernel-audit60-20261004','elliptic-positive-certificate60-20261004','elliptic-positive-certificate60-independent-audit-20261004','nonelliptic-quadratic-certificate60-20261004','nonelliptic-quadratic-certificate-audit60-20261004']
rows={}
for name in NAMES:
    root=BASE/name
    for p in sorted([root,*root.rglob('*')]):
        s=p.lstat()
        row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'size':s.st_size,'type':'dir' if p.is_dir() else 'file'}
        if p.is_symlink(): raise RuntimeError('Unexpected symlink: '+str(p))
        if p.is_file(): row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
        rows[str(p.relative_to(BASE))]=row
out=Path(sys.argv[1]); out.write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
print(json.dumps({'entries':len(rows),'files':sum(r['type']=='file' for r in rows.values()),'output':str(out)},sort_keys=True))
