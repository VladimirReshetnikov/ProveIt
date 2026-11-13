#!/usr/bin/env python3
"""Synthetic Linux process-handle review. Never runs Lean or a real worker."""
import ast
import ctypes
import errno
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run python3 -I -S -B')
if sys.platform!='linux' or platform.machine()!='x86_64':
    raise SystemExit('x86_64 Linux required')
HERE=Path(__file__).resolve().parent
pins={'author-README.md':'eeab33c7b246ccf95396134f6722afdf6d0af9567ec44cebcb33cf2f410b5dae',
      'author-check.py':'cecd0bad53aa459415f5087b487acb2adbd029c390bda4ec5a449c00556fcb05',
      'author-result.json':'360e31a418539f849ad819df05d0751c490b2517afd34accb1fbcfe0d155dfac'}
for name,h in pins.items():
    if hashlib.sha256((HERE/name).read_bytes()).hexdigest()!=h:raise RuntimeError('snapshot mismatch '+name)
source=(HERE/'author-check.py').read_text()
for node in ast.walk(ast.parse(source)):
    if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
        if node.func.attr in ('kill','killpg','terminate'):
            raise RuntimeError('numeric or subprocess kill fallback present')
assert "os.open('stat',os.O_RDONLY,dir_fd=procfd)" in source
assert 'send(fd,signum)' in source and 'os.WNOWAIT' in source

observed=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'author-check.py')],
                        capture_output=True,text=True,timeout=35,check=True)
if json.loads(observed.stdout)!=json.loads((HERE/'author-result.json').read_text()):
    raise RuntimeError('synthetic prototype result did not reproduce')

libc=ctypes.CDLL(None,use_errno=True);libc.syscall.restype=ctypes.c_long
def send(fd,sig):
    r=libc.syscall(ctypes.c_long(424),ctypes.c_int(fd),ctypes.c_int(sig),ctypes.c_void_p(0),ctypes.c_uint(0))
    if r<0:raise OSError(ctypes.get_errno(),os.strerror(ctypes.get_errno()))
def sess(fd):
    p=os.open('stat',os.O_RDONLY,dir_fd=fd)
    try:return int(os.read(p,8192).decode().rsplit(')',1)[1].split()[3])
    finally:os.close(p)

children=[];fds=[];stale_errno=None;bystander_alive=False
try:
    for _ in range(2):
        p=subprocess.Popen([sys.executable,'-I','-S','-B','-c','import time;time.sleep(5)'],
            start_new_session=True,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        children.append(p)
        fd=os.open('/proc/'+str(p.pid),os.O_RDONLY|os.O_DIRECTORY);fds.append(fd)
        assert sess(fd)==p.pid
    send(fds[0],signal.SIGTERM);children[0].wait(timeout=3)
    try:send(fds[0],0)
    except OSError as exc:stale_errno=exc.errno
    assert stale_errno==errno.ESRCH,'stale handle did not report ESRCH'
    bystander_alive=children[1].poll() is None
    assert bystander_alive,'separate-session bystander exited'
finally:
    for index,p in enumerate(children):
        if p.poll() is None and index<len(fds):
            try:send(fds[index],signal.SIGTERM)
            except OSError:pass
    for p in children:
        # Children also have a five-second natural exit; no numeric kill fallback.
        if p.poll() is None:p.wait(timeout=7)
    for fd in fds:os.close(fd)
print(json.dumps({'status':'PASS_SYNTHETIC_ONLY','prototype_controls':'reproduced',
 'stale_open_proc_handle_errno':stale_errno,'separate_bystander_alive':bystander_alive,
 'numeric_kill_fallback_in_source':False,
 'scope':'Synthetic proc-handle controls; no PID reuse forced, Lean or production traversal.'},sort_keys=True))
