#!/usr/bin/env python3
"""Capture independent and author external checks without modifying drafts."""
from pathlib import Path
from hashlib import sha256
import json, subprocess, sys
assert sys.flags.isolated and sys.flags.no_site and __debug__
here=Path(__file__).resolve().parent
d=here.parents[1]
author=d/'research/ordinary12-ipra-bridge/compact44-free-j-display-draft/check_display.py'
files=[here/'audit.py',author]
def sha(p):return sha256(p.read_bytes()).hexdigest()
before={str(p):sha(p) for p in files}
results={}
for name,args in [('independent',[str(files[0])]),('author94',[str(author),'--variant','94']),('author95',[str(author),'--variant','95'])]:
    cmd=[sys.executable,'-I','-S','-B',*args]
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
    (here/(name+'.stdout')).write_bytes(p.stdout);(here/(name+'.stderr')).write_bytes(p.stderr)
    results[name]={'exit':p.returncode,'stdout_sha256':sha(here/(name+'.stdout')),'stderr_sha256':sha(here/(name+'.stderr'))}
    if p.returncode or p.stderr: raise RuntimeError((name,p.returncode,p.stderr.decode(errors='replace')))
if before!={str(p):sha(p) for p in files}:raise RuntimeError('source changed during run')
(here/'terminal.json').write_text(json.dumps({'status':'PASS','source_hashes':before,'checks':results},indent=2,sort_keys=True)+'\n')
print('PASS',json.dumps(results,sort_keys=True))
