#!/usr/bin/env python3
"""Capture the K/four-port source and artifact audit."""
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys

here=Path(__file__).resolve().parent
audit=here/'audit.py'
out=here/'observations/attempt01'
pin='317cccc35d2317ef5256b971b9da3759cd20e6502f9be64c67cc3ed584f363de'
if out.exists():raise RuntimeError('refusing to overwrite observation')
before=audit.read_bytes()
if sha256(before).hexdigest()!=pin:raise RuntimeError('audit source drift')
out.mkdir(parents=True)
(out/'source.py').write_bytes(before)
command=[sys.executable,'-I','-S','-B',str(audit)]
run=subprocess.run(command,capture_output=True,text=True,timeout=180)
(out/'stdout').write_text(run.stdout)
(out/'stderr').write_text(run.stderr)
receipt={'command':command,'exit_code':run.returncode,'source_sha256':pin,
         'source_unchanged':audit.read_bytes()==before,
         'stdout_sha256':sha256(run.stdout.encode()).hexdigest(),
         'stderr_sha256':sha256(run.stderr.encode()).hexdigest()}
(out/'terminal.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,sort_keys=True))
if run.returncode!=0 or run.stderr or not receipt['source_unchanged']:raise SystemExit(1)
