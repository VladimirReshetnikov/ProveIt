"""New static utility: snapshot release metadata and copy regular inputs using O_NOATIME.
Never executes release content and never writes within release.
"""
import os, json, hashlib, stat
from pathlib import Path
src=Path('/workspace/shared/report65-clocked-native-gaps-release-20261004')
out=Path('/workspace/shared/report65-manuscript-independent-review-20261004')
records=[]
def visit(path):
    st=os.stat(path,follow_symlinks=False)
    rel=str(path.relative_to(src))
    rec={'path':rel,'mode':oct(stat.S_IMODE(st.st_mode)),'size':st.st_size,'atime_ns':st.st_atime_ns,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
    if stat.S_ISDIR(st.st_mode):
        records.append(rec)
        fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY|os.O_NOATIME)
        try:
            entries=sorted(os.listdir(fd))
        finally: os.close(fd)
        for entry in entries: visit(path/entry)
    elif stat.S_ISREG(st.st_mode):
        fd=os.open(path,os.O_RDONLY|os.O_NOATIME)
        with os.fdopen(fd,'rb') as f: data=f.read()
        rec['sha256']=hashlib.sha256(data).hexdigest(); records.append(rec)
        dest=out/'inputs'/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
    else: raise RuntimeError('Unexpected nonregular input: '+str(path))
visit(src)
(out/'review'/'release_snapshot_before.json').write_text(json.dumps(records,indent=2)+'\n')
print('\n'.join(f"{r['path']} {r.get('sha256','')}" for r in records))
