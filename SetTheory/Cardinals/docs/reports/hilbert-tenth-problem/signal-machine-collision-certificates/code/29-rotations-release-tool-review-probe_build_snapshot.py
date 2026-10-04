#!/usr/bin/env python3
"""Exercise only the inspected build tool's read-only snapshot function."""
import hashlib,json,runpy,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
PRISTINE=HERE/'scratch/pristine'
RESULTS=[]
for case in ('missing-frozen-directory','symlink-frozen-directory','symlink-manuscript-directory','unexpected-fifo'):
    root=HERE/'scratch'/('probe-'+case)
    shutil.copytree(PRISTINE,root,symlinks=True)
    directory='manuscript' if case=='symlink-manuscript-directory' else 'real-input'
    if case!='unexpected-fifo':
        shutil.rmtree(root/directory)
        if case.startswith('symlink'):(root/directory).symlink_to(PRISTINE/directory,target_is_directory=True)
    else:
        import os
        os.mkfifo(root/directory/'UNEXPECTED_FIFO')
    module=runpy.run_path(str(root/'tools/build_report59.py'),run_name='inspected_snapshot_probe')
    try:
        value=module['snapshot']()
        result={'case':case,'accepted':True,'files':len(value),'inspected_directory_entries':sorted(n for n in value if n.startswith(directory+'/'))}
    except Exception as e:result={'case':case,'accepted':False,'error':str(e)}
    RESULTS.append(result)
    shutil.rmtree(root)
(HERE/'SNAPSHOT_PROBES.json').write_text(json.dumps(RESULTS,sort_keys=True,indent=2)+'\n')
print(json.dumps(RESULTS,sort_keys=True,indent=2))
