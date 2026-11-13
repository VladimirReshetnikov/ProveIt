#!/usr/bin/env python3
"""Capture the independent source/artifact/degree audit without invoking Lean."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import time

H=Path(__file__).resolve().parent
S=H/'audit.py'
O=H/'observations/attempt01'
if O.exists():
    raise RuntimeError('refusing to overwrite observation')
O.mkdir(parents=True)
source=S.read_bytes()
(O/'source.py').write_bytes(source)
cmd=['python3','-I','-S','-B',str(S)]
start=time.monotonic()
try:
    proc=subprocess.run(cmd,capture_output=True,timeout=180)
    code,stdout,stderr=proc.returncode,proc.stdout,proc.stderr
except subprocess.TimeoutExpired as exc:
    code,stdout,stderr=None,exc.stdout or b'',exc.stderr or b''
(O/'stdout').write_bytes(stdout)
(O/'stderr').write_bytes(stderr)
receipt={'command':cmd,'exit_code':code,'duration_seconds':round(time.monotonic()-start,3),
         'source_sha256':sha256(source).hexdigest(),
         'source_unchanged':S.read_bytes()==source,
         'stdout_sha256':sha256(stdout).hexdigest(),'stderr_sha256':sha256(stderr).hexdigest()}
(O/'terminal.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,sort_keys=True))
if code != 0 or stderr or S.read_bytes()!=source:
    raise SystemExit(1)
