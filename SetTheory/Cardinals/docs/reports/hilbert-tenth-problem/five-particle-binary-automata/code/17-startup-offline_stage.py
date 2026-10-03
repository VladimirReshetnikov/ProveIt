#!/usr/bin/env python3
"""Execute one bundled script with network and out-of-bundle data reads denied.
This standard-library audit guard is a reproducibility check, not a security
sandbox against malicious Python/native code. Operating-system libraries and
Python's own installation remain accessible for the interpreter runtime.
"""
import os
from pathlib import Path
import runpy
import sys
import sysconfig
ROOT = Path(__file__).resolve().parent
SCRIPT = Path(sys.argv[1]).resolve()
if not SCRIPT.is_relative_to(ROOT) or not SCRIPT.is_file():
    raise RuntimeError('Only bundled or temporary generated scripts are allowed')
# Isolated Python startup ignores user site-packages and PYTHONPATH.
sys.dont_write_bytecode = True
runtime = {Path(sysconfig.get_path(key)).resolve() for key in ('stdlib', 'platstdlib')}
runtime.add(Path(sys.executable).resolve())

def allowed_read(path):
    return path.is_relative_to(ROOT) or any(path == base or path.is_relative_to(base) for base in runtime)

def guard(event, args):
    if event.startswith('socket.') or event.startswith('urllib.'):
        raise RuntimeError('Network access is forbidden during offline replay')
    if event == 'open':
        raw, mode, flags = args
        if isinstance(raw, int):
            return
        path = Path(os.fsdecode(raw)).resolve()
        writing = bool(flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))
        if (writing and not path.is_relative_to(ROOT)) or (not writing and not allowed_read(path)):
            raise RuntimeError('Out-of-bundle file access forbidden: '+path.name)
    if event in ('os.listdir', 'os.scandir') and args and not isinstance(args[0], int):
        path = Path(os.fsdecode(args[0] if args[0] is not None else '.')).resolve()
        if not allowed_read(path):
            raise RuntimeError('Out-of-bundle directory access forbidden: '+path.name)
    if event == 'subprocess.Popen':
        executable, arguments = args[0], args[1]
        if Path(executable).resolve() != Path(sys.executable).resolve() or str(ROOT / 'offline_stage.py') not in arguments:
            raise RuntimeError('Only guarded Python subprocesses are allowed')

sys.addaudithook(guard)
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(SCRIPT.parent))
sys.argv = [str(SCRIPT)] + sys.argv[2:]
runpy.run_path(str(SCRIPT), run_name='__main__')
