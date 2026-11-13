#!/usr/bin/env python3
"""Capture v2 and earlier independent and author display checks."""
from pathlib import Path
from hashlib import sha256
import json, subprocess, sys
assert sys.flags.isolated and sys.flags.no_site and __debug__
here=Path(__file__).resolve().parent
d=here.parents[1]
oldreview=d/'reviews/ordinary12-decimal-displays-independent-review/audit.py'
v2author=d/'research/ordinary12-ipra-bridge/compact44-free-j-display-v2/check_display.py'
oldauthor=d/'research/ordinary12-ipra-bridge/compact44-free-j-display-draft/check_display.py'
sources=[here/'audit.py',oldreview,v2author,oldauthor]
def sha(p):return sha256(p.read_bytes()).hexdigest()
before={str(p):sha(p) for p in sources}
checks=[('v2_independent',[str(sources[0])]),('original_independent',[str(oldreview)]),('v2_author94',[str(v2author),'--variant','94']),('v2_author95',[str(v2author),'--variant','95']),('original_author94',[str(oldauthor),'--variant','94']),('original_author95',[str(oldauthor),'--variant','95'])]
results={}
for name,args in checks:
    p=subprocess.run([sys.executable,'-I','-S','-B',*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
    (here/(name+'.stdout')).write_bytes(p.stdout);(here/(name+'.stderr')).write_bytes(p.stderr)
    results[name]={'exit':p.returncode,'stdout_sha256':sha(here/(name+'.stdout')),'stderr_sha256':sha(here/(name+'.stderr'))}
    if p.returncode or p.stderr:raise RuntimeError((name,p.returncode,p.stderr.decode(errors='replace')))
if before!={str(p):sha(p) for p in sources}:raise RuntimeError('source changed during run')
(here/'terminal.json').write_text(json.dumps({'status':'PASS','source_hashes':before,'checks':results},indent=2,sort_keys=True)+'\n')
print('PASS',json.dumps(results,sort_keys=True))
