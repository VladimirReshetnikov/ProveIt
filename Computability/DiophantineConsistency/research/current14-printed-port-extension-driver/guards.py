"""Small explicit file guards shared by the extension driver and its controls."""
import hashlib
import os
from pathlib import Path

SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()

def scan(stem):
    out={}
    for suffix in SUFFIXES:
        path=Path(str(stem)+suffix)
        if os.path.lexists(path):
            if not path.is_file():raise ValueError(('broken or non-file companion',str(path)))
            out[str(path)]={'realpath':str(path.resolve()),'sha256':digest(path)}
        else:out[str(path)]=None
    return out

def check_guard(guard):
    for name,expected in guard.items():
        path=Path(name)
        if expected is None:
            if os.path.lexists(path):raise ValueError(('unexpected file',name))
        elif not path.is_file() or str(path.resolve())!=expected['realpath'] or digest(path)!=expected['sha256']:
            raise ValueError(('input changed',name))

def capture_output(path,expected_sha256):
    path=Path(path)
    if not str(path).endswith('.olean') or not path.is_file() or path.is_symlink():
        raise ValueError(('invalid producer object',str(path)))
    guard=scan(Path(str(path)[:-6]))
    expected={'realpath':str(path.absolute()),'sha256':expected_sha256}
    if guard[str(path)]!=expected:
        raise ValueError(('producer object differs from recorded output',str(path)))
    return guard

def capture_input(path,recorded_sha256):
    path=Path(path)
    if not str(path).endswith('.olean'):
        raise ValueError(('invalid direct object',str(path)))
    guard=scan(Path(str(path)[:-6]))
    entry=guard[str(path)]
    if not isinstance(entry,dict) or entry['sha256']!=recorded_sha256:
        raise ValueError(('direct object differs from recorded input',str(path)))
    return guard

def reject_project_fallbacks(roots,tops):
    for root in roots:
        for top in tops:
            for suffix in ('',*SUFFIXES,'.so','.dll','.dylib'):
                path=Path(root)/(top+suffix)
                if os.path.lexists(path):raise ValueError(('project fallback',str(path)))
