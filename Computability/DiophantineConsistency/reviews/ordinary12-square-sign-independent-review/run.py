#!/usr/bin/env python3
"""Capture the full independent square-sign search audit."""
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys

here=Path(__file__).resolve().parent
source=here/'audit.py'
output=here/'observations-attempt02'
terminal=here/'terminal-attempt02'
pin='eda47d0d076ae1f1491a223bddb47951071f8fe458fbf86c9cbee5f816642193'
if output.exists() or terminal.exists(): raise RuntimeError('output already exists')
before=source.read_bytes()
if sha256(before).hexdigest()!=pin: raise RuntimeError('audit source drift')
terminal.mkdir()
command=[sys.executable,'-I','-B',str(source),str(output)]
run=subprocess.run(command,capture_output=True,text=True,timeout=180)
(terminal/'stdout').write_text(run.stdout)
(terminal/'stderr').write_text(run.stderr)
result=output/'audit.json'
receipt={'command':command,'exit_code':run.returncode,'source_sha256':pin,
 'source_unchanged':source.read_bytes()==before,
 'stdout_sha256':sha256(run.stdout.encode()).hexdigest(),
 'stderr_sha256':sha256(run.stderr.encode()).hexdigest(),
 'result_sha256':sha256(result.read_bytes()).hexdigest() if result.is_file() else None}
(terminal/'terminal.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,sort_keys=True))
if run.returncode!=0 or run.stderr or not result.is_file() or not receipt['source_unchanged']:
    raise SystemExit(1)
