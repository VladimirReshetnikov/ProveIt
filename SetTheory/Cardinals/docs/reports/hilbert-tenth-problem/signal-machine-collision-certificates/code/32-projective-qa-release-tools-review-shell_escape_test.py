#!/usr/bin/env python3
"""Check pdfTeX's actual shell-escape primitive on an owned synthetic manuscript."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

BASE=Path(__file__).absolute().parent/'final-run'
ROOT=BASE/'shell-escape-fixture'
shutil.copytree(BASE/'author-selftest-replay/fixture',ROOT,copy_function=shutil.copy2)
marker=BASE/'UNEXPECTED_TEX_SHELL_EXECUTION'
(ROOT/'manuscript/evidence.tex').write_text('\\ifnum\\pdfshellescape=0\\relax\\else\\errmessage{Shell escape is not disabled}\\fi\n\\typeout{INDEPENDENT-SHELL-ESCAPE-IS-ZERO}\n\\immediate\\write18{touch '+str(marker)+'}\n')

def run(tool,args):
    p=subprocess.run([sys.executable,'-I','-S','-B',str(ROOT/'tools'/tool),*args],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    if p.returncode:
        raise RuntimeError(p.stdout.decode(errors='replace'))
    return p.stdout.decode()

prepared=BASE/'shell-escape-prepared'
run('release62.py',['prepare','--output-dir',str(prepared)])
shutil.copy2(prepared/'Report62.tex',ROOT/'Report62.tex')
shutil.copy2(prepared/'MANUSCRIPT_PINS.json',ROOT/'manuscript/MANUSCRIPT_PINS.json')
pin=hashlib.sha256((ROOT/'manuscript/MANUSCRIPT_PINS.json').read_bytes()).hexdigest()
lock=hashlib.sha256((ROOT/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()).hexdigest()
out=BASE/'shell-escape-build'
stdout=run('build_report62.py',['--pins-sha',pin,'--dependency-lock-sha',lock,'--output-dir',str(out)])
if marker.exists() or not all(b'INDEPENDENT-SHELL-ESCAPE-IS-ZERO' in (out/('compile-'+str(n)+'.stdout')).read_bytes() for n in range(1,4)):
    raise RuntimeError('Shell-escape control did not hold')
result={'status':'PASS','test_count':1,'scope':'Owned synthetic TeX only','primitive_zero_on_all_three_passes':True,'write18_marker_absent':True,'builder_sha256':hashlib.sha256((ROOT/'tools/build_report62.py').read_bytes()).hexdigest(),'release_sha256':hashlib.sha256((ROOT/'tools/release62.py').read_bytes()).hexdigest(),'build_stdout':stdout}
(BASE/'SHELL_ESCAPE_RESULT.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps(result))
