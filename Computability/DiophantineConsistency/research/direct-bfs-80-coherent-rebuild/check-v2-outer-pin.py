#!/usr/bin/env python3
"""Check the actual wrapper rejects a modified runner before starting it."""
from hashlib import sha256
from pathlib import Path
import json, shutil, subprocess, sys, tempfile
h=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='bfs-outer-v2-mutation-') as d:
    d=Path(d);shutil.copyfile(h/'run-v2-outer.py',d/'run-v2-outer.py')
    (d/'run-v2.py').write_text('raise SystemExit(0)\n')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'run-v2-outer.py'),'--attempt','attempt01'],capture_output=True,text=True)
    if p.returncode==0 or 'reviewed runner SHA mismatch before launch' not in p.stderr or (d/'observations/attempt01').exists():raise RuntimeError('wrapper mutation not rejected before child')
    print(json.dumps({'status':'PASS','outer_sha256':sha256((h/'run-v2-outer.py').read_bytes()).hexdigest(),'child_started':False,'exit':p.returncode,'stderr':p.stderr.strip()},indent=2))
