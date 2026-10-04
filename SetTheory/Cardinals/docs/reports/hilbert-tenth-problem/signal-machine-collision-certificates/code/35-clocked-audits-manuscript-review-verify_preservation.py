"""Fresh read-only release comparison using O_NOATIME. Never writes the source tree."""
import os,json,hashlib,stat
from pathlib import Path
root=Path('/workspace/shared/report65-manuscript-independent-review-20261004')
src=Path('/workspace/shared/report65-clocked-native-gaps-release-20261004')
before=json.loads((root/'review'/'release_snapshot_before.json').read_text()); after=[]
def visit(path):
    st=os.stat(path,follow_symlinks=False); rel=str(path.relative_to(src))
    r={'path':rel,'mode':oct(stat.S_IMODE(st.st_mode)),'size':st.st_size,'atime_ns':st.st_atime_ns,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
    if stat.S_ISDIR(st.st_mode):
        after.append(r); fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY|os.O_NOATIME)
        try: entries=sorted(os.listdir(fd))
        finally: os.close(fd)
        for e in entries: visit(path/e)
    else:
        fd=os.open(path,os.O_RDONLY|os.O_NOATIME)
        with os.fdopen(fd,'rb') as f: data=f.read()
        r['sha256']=hashlib.sha256(data).hexdigest(); after.append(r)
visit(src)
(root/'review'/'release_snapshot_after.json').write_text(json.dumps(after,indent=2)+'\n')
b={r['path']:r for r in before}; a={r['path']:r for r in after}
differences=[{'path':p,'before':b.get(p),'after':a.get(p)} for p in sorted(set(a)|set(b)) if a.get(p)!=b.get(p)]
result={'unchanged_since_review_baseline':not differences,'object_count':len(before),'differences':differences,'scope':'The initial directory listing preceded the baseline; historical directory-atime invariance before that listing is not claimed. No source metadata was reset. Final layout was read separately from the author-owned build tree.'}
(root/'review'/'preservation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
