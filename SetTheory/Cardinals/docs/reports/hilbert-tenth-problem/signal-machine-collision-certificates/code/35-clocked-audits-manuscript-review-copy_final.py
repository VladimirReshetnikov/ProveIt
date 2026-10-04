"""Read only two requested final candidate files and the declared layout patch with O_NOATIME."""
import os, json, hashlib, stat, difflib
from pathlib import Path
root=Path('/workspace/shared/report65-manuscript-independent-review-20261004')
(root/'final-inputs').mkdir(exist_ok=True)
records=[]
for src in [Path('/workspace/shared/report65-build-e-20261004/Report65.pdf'),Path('/workspace/shared/report65-build-e-20261004/Report65.tex'),Path('/workspace/shared/report65-author-qa-20261004/FINAL_LAYOUT.patch')]:
    a=os.stat(src); fd=os.open(src,os.O_RDONLY|os.O_NOATIME)
    with os.fdopen(fd,'rb') as f: data=f.read()
    b=os.stat(src)
    fields=('st_mode','st_size','st_atime_ns','st_mtime_ns','st_ctime_ns')
    assert all(getattr(a,x)==getattr(b,x) for x in fields)
    (root/'final-inputs'/src.name).write_bytes(data)
    records.append({'source':str(src),'sha256':hashlib.sha256(data).hexdigest(),'metadata_before_and_after':{x:getattr(a,x) for x in fields}})
(root/'review'/'final_copy_preservation.json').write_text(json.dumps(records,indent=2)+'\n')
old=(root/'inputs'/'Report65.tex').read_text().splitlines(keepends=True)
new=(root/'final-inputs'/'Report65.tex').read_text().splitlines(keepends=True)
diff=''.join(difflib.unified_diff(old,new,fromfile='original-pinned-Report65.tex',tofile='final-pinned-Report65.tex'))
(root/'review'/'independent_final_delta.patch').write_text(diff)
print(json.dumps(records,indent=2)); print(diff)
