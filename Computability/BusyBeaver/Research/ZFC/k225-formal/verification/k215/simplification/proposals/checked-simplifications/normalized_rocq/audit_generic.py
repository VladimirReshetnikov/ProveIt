#!/usr/bin/env python3
"""Separate recursive kernel check of the new generic normalized checker."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent
WORK=ROOT/'verification/work';LOG=ROOT/'verification/logs/coqchk_generic.log'
command=[shutil.which('coqchk'),'-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F','-silent','NormalizedBisim']
start=time.monotonic()
with LOG.open('w') as stream:
 p=subprocess.Popen(command,cwd=WORK,stdout=stream,stderr=subprocess.STDOUT)
 _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
r={'command':command,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,'scope':'Recursive check of generic normalized certificate soundness; concrete source theorem separately kernel-checked by compilation','log_sha256':hashlib.sha256(LOG.read_bytes()).hexdigest(),'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'verification/generic-kernel-result.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
raise SystemExit(p.returncode)
