#!/usr/bin/env python3
"""Demonstrate that the native loader executes before Python isolation."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
DRIVER=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-parent-window/replay.py'
CODE=r'''
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
__attribute__((constructor)) static void mark(void) {
  const char *p = getenv("PREFIX_LOADER_CANARY");
  if (p) { int f = open(p, O_WRONLY | O_CREAT | O_TRUNC, 0600); if (f >= 0) { write(f, "loaded", 6); close(f); } }
}
'''
with tempfile.TemporaryDirectory(prefix='prefix-loader-control-') as t:
    root=Path(t);c=root/'canary.c';so=root/'canary.so';marker=root/'loaded';c.write_text(CODE)
    subprocess.run(['cc','-shared','-fPIC','-o',str(so),str(c)],check=True,capture_output=True)
    env=os.environ.copy();env['LD_PRELOAD']=str(so);env['PREFIX_LOADER_CANARY']=str(marker)
    p=subprocess.run([sys.executable,'-I','-S',str(DRIVER),'--output','/tmp/not-a-prefix'],env=env,capture_output=True,timeout=30)
    if p.returncode==0 or not marker.exists() or marker.read_text()!='loaded' or b'fresh direct' not in p.stderr:
        raise ValueError(('loader canary unexpectedly suppressed',p.returncode,p.stderr))
print('PASS_INITIAL_LOADER_CANARY_EXECUTED_BEFORE_DRIVER_GUARD')
