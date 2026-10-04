#!/usr/bin/env python3
"""Release-only authenticated replay of the unchanged independent audit checker.

All science is inert data. A narrow per-exec import facade routes the checker's
historical paths without changing its source bytes. This is NOT an OS/network
sandbox. Trust the Python/SymPy runtime and use a quiescent POSIX filesystem.
"""
import argparse
import builtins
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import sys
from types import SimpleNamespace

PINS_SHA256 = 'd20b85535be14fb12c2494447b8326dc260310c2d9441677f48866eb6e2658f8'
CHECKER = 'independent_static_audit.py'
CHECKER_SHA256 = 'a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec'
HISTORICAL_SCIENCE = '/workspace/shared/projective-signal-shears62-20261004'
GOLDEN = ('independent_checks.json', 'rule44_static_review.json')
GENERATED = ('frozen_after.json',) + GOLDEN

class Rejected(Exception):
    pass

def need(condition, message):
    if not condition:
        raise Rejected(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def meta(st):
    return (st.st_dev, st.st_ino, st.st_mode, st.st_nlink, st.st_size, st.st_mtime_ns)

def canonical(raw, fresh=False):
    need(isinstance(raw,str), 'non-string path')
    p=Path(raw)
    need(p.is_absolute() and str(p)==raw and '..' not in p.parts and not raw.startswith('//'),
         'path must have canonical absolute spelling: '+raw)
    current=Path('/')
    for i,part in enumerate(p.parts[1:]):
        current=current/part
        last=i==len(p.parts)-2
        try:
            st=current.lstat()
        except FileNotFoundError:
            need(fresh and last,'missing input or output parent: '+str(current))
            return p
        need(not stat.S_ISLNK(st.st_mode),'symbolic-link component: '+str(current))
        need(last or stat.S_ISDIR(st.st_mode),'non-directory ancestor: '+str(current))
    need(not fresh,'output must be fresh and nonexistent: '+raw)
    return p

def overlap(a,b):
    return a==b or a in b.parents or b in a.parents

def read_file(p):
    before=p.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink==1,
         'only regular single-link files are accepted: '+str(p))
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        need(meta(os.fstat(fd))==meta(before),'changed file while opening: '+str(p))
        with os.fdopen(fd,'rb',closefd=False) as f:
            data=f.read()
        need(meta(os.fstat(fd))==meta(before),'changed file while reading: '+str(p))
    finally:
        os.close(fd)
    need(meta(p.lstat())==meta(before),'changed file path: '+str(p))
    return data,meta(before)

def unique_pairs(pairs):
    result={}
    for k,v in pairs:
        need(k not in result,'duplicate JSON key: '+k)
        result[k]=v
    return result

def relative_name(name, allow_root=False):
    need(isinstance(name,str),'non-string inventory path')
    if allow_root and name=='.':
        return
    need(name!='' and not name.startswith('/') and '\\' not in name and
         all(part not in ('','.','..') for part in name.split('/')) and
         str(Path(name))==name,'malformed relative inventory path: '+repr(name))

def validate_pins(pins):
    need(type(pins) is dict and set(pins)=={'format','roots'} and type(pins['format']) is int and pins['format']==1,'bad pins schema')
    need(type(pins['roots']) is dict and set(pins['roots'])=={'science','audit'},'bad pinned roots')
    for root in pins['roots'].values():
        need(type(root) is dict and set(root)=={'directories','files'},'bad inventory schema')
        dirs,files=root['directories'],root['files']
        need(type(dirs) is list and type(files) is dict,'bad inventory types')
        for name in dirs:relative_name(name,True)
        need(len(set(dirs))==len(dirs) and '.' in dirs,'duplicate/missing root directory')
        for name,entry in files.items():
            relative_name(name)
            need(type(entry) is dict and set(entry)=={'bytes','sha256'},'bad file pin schema')
            need(type(entry['bytes']) is int and entry['bytes']>=0 and
                 isinstance(entry['sha256'],str) and re.fullmatch('[0-9a-f]{64}',entry['sha256']) is not None,'bad file size or digest')
        need(set(dirs).isdisjoint(files),'file-directory pin collision')
        for name in set(dirs)|set(files):
            if name!='.':need(str(Path(name).parent) in dirs,'missing parent directory pin: '+name)

def inventory(root,pins):
    expected=set(pins['directories'])|set(pins['files'])
    seen=set(); snapshots={}; contents={}
    def visit(rel):
        p=root if rel=='.' else root/rel
        st=p.lstat()
        need(not stat.S_ISLNK(st.st_mode),'symbolic-link inventory entry: '+str(p))
        need(rel in expected,'extra inventory entry: '+str(p))
        seen.add(rel)
        if stat.S_ISDIR(st.st_mode):
            need(rel in pins['directories'],'unexpected directory type: '+str(p))
            snapshots[rel]=meta(st)
            with os.scandir(p) as scan:names=sorted(entry.name for entry in scan)
            for name in names:visit(name if rel=='.' else rel+'/'+name)
        else:
            need(rel in pins['files'],'unexpected non-directory type: '+str(p))
            data,metadata=read_file(p)
            wanted=pins['files'][rel]
            need(len(data)==wanted['bytes'] and digest(data)==wanted['sha256'],'input byte/hash mismatch: '+str(p))
            snapshots[rel]=metadata;contents[rel]=data
    visit('.')
    need(seen==expected,'missing inventory entries: '+repr(sorted(expected-seen)))
    return snapshots,contents

def exclusive(p,data):
    fd=os.open(p,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,'wb') as f:f.write(data)

def snapshot_for_checker(root):
    rows=[]
    for p in [root]+sorted(root.rglob('*')):
        st=p.lstat()
        row={'path':'.' if p==root else str(p.relative_to(root)),
             'mode':oct(stat.S_IMODE(st.st_mode)),'mtime_ns':st.st_mtime_ns,
             'size':st.st_size,'kind':'file' if p.is_file() else 'directory'}
        if p.is_file():row['sha256']=digest(read_file(p)[0])
        rows.append(row)
    return (json.dumps(rows,indent=2)+'\n').encode()

def execute_owned_checker(source,science,audit,output):
    """Execute exact source bytes with optimize=0 and a local import facade.

    Actual source metadata is never faked. Its relocation-specific before
    snapshot is generated outside the immutable audit; all output goes outside.
    Only this exec's import of pathlib is changed; no global module is patched.
    """
    evidence=output/'evidence'
    evidence.mkdir(mode=0o700)
    exclusive(evidence/'frozen_before.json',snapshot_for_checker(science))
    checker_file=audit/CHECKER
    allowed_reads={science,audit,output}
    class RoutedPath:
        def __init__(self,p,*,historical=True):
            raw=os.fspath(p)
            self.p=science if historical and raw==HISTORICAL_SCIENCE else Path(raw)
            need(any(self.p==root or root in self.p.parents for root in allowed_reads),'checker path outside routed roots: '+raw)
        def __fspath__(self):return str(self.p)
        def __str__(self):return str(self.p)
        def __eq__(self,other):return isinstance(other,RoutedPath) and self.p==other.p
        def __lt__(self,other):return self.p<other.p
        def __truediv__(self,part):
            return RoutedPath(evidence if self.p==audit and part=='evidence' else self.p/part,historical=False)
        @property
        def parent(self):return RoutedPath(self.p.parent,historical=False)
        def resolve(self):return RoutedPath(self.p.resolve(strict=True),historical=False)
        def relative_to(self,other):return self.p.relative_to(other.p)
        def rglob(self,pattern):return (RoutedPath(p,historical=False) for p in self.p.rglob(pattern))
        def lstat(self):return self.p.lstat()
        def stat(self):return self.p.stat()
        def is_file(self):return self.p.is_file()
        def read_bytes(self):return read_file(self.p)[0]
        def read_text(self):return self.read_bytes().decode('utf-8')
        def write_text(self,text):
            need(self.p.parent==evidence and self.p.name in GENERATED,'unexpected checker write: '+str(self.p))
            data=text.encode('utf-8');exclusive(self.p,data);return len(text)
    original_import=builtins.__import__
    def local_import(name,globals=None,locals=None,fromlist=(),level=0):
        if name=='pathlib' and level==0:
            need(tuple(fromlist)==('Path',),'unexpected pathlib import')
            return SimpleNamespace(Path=RoutedPath)
        return original_import(name,globals,locals,fromlist,level)
    environment={'__name__':'__main__','__file__':str(checker_file),
                 '__builtins__':dict(vars(builtins),__import__=local_import)}
    stdout,stderr=io.StringIO(),io.StringIO()
    with contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr):
        exec(compile(source,str(checker_file),'exec',dont_inherit=True,optimize=0),environment)
    need(stderr.getvalue()=='','checker produced stderr')
    return stdout.getvalue().encode('utf-8')

def run(args):
    need(hasattr(os,'O_NOFOLLOW'),'POSIX O_NOFOLLOW is required')
    science=canonical(args.science_root);audit=canonical(args.audit_root)
    pins_path=canonical(args.pins);output=canonical(args.output_root,True)
    adapter=canonical(os.path.abspath(__file__));adapter_dir=adapter.parent
    need(not overlap(science,audit),'science and audit overlap')
    need(not overlap(science,adapter_dir) and not overlap(audit,adapter_dir),'inputs overlap adapter directory')
    need(not overlap(output,pins_path),'output overlaps pins')
    for root in (science,audit,adapter_dir):need(not overlap(output,root),'output overlaps protected input/adapter')
    pin_bytes,pin_meta=read_file(pins_path)
    need(digest(pin_bytes)==PINS_SHA256,'pins file authentication failed')
    pins=json.loads(pin_bytes,object_pairs_hook=unique_pairs);validate_pins(pins)
    s_before,s_data=inventory(science,pins['roots']['science'])
    a_before,a_data=inventory(audit,pins['roots']['audit'])
    identities=set();protected_dirs={meta(adapter_dir.lstat())[:2]}
    for snapshot in (s_before,a_before):
        for name,entry in snapshot.items():
            need(entry[:2] not in identities,'aliased input object: '+name)
            identities.add(entry[:2])
            if stat.S_ISDIR(entry[2]):protected_dirs.add(entry[:2])
    for parent in output.parents:need(meta(parent.lstat())[:2] not in protected_dirs,'output parent aliases protected directory')
    source=a_data[CHECKER]
    need(digest(source)==CHECKER_SHA256,'owned checker authentication failed')
    # SymPy is trusted installed runtime; its version is part of golden evidence.
    import sympy
    need(sympy.__version__=='1.14.0','replay requires trusted SymPy 1.14.0')
    output.mkdir(mode=0o700,exist_ok=False)
    try:
        stdout=execute_owned_checker(source,science,audit,output)
    finally:
        s_after,_=inventory(science,pins['roots']['science'])
        a_after,_=inventory(audit,pins['roots']['audit'])
        p_after,p_meta_after=read_file(pins_path)
        need(s_before==s_after and a_before==a_after,'input metadata changed during replay')
        need(p_after==pin_bytes and p_meta_after==pin_meta,'pins changed during replay')
    expected_stdout=a_data['evidence/run_stdout.json']
    need(stdout==expected_stdout,'checker stdout differs byte-for-byte')
    for name in GOLDEN:
        need(read_file(output/'evidence'/name)[0]==a_data['evidence/'+name],'golden evidence differs byte-for-byte: '+name)
    before=read_file(output/'evidence/frozen_before.json')[0]
    after=read_file(output/'evidence/frozen_after.json')[0]
    need(before==after,'fresh transport preservation snapshots differ byte-for-byte')
    need(set(p.name for p in output.iterdir())=={'evidence'},'unexpected output root entry')
    need(set(p.name for p in (output/'evidence').iterdir())==set(GENERATED)|{'frozen_before.json'},'unexpected evidence output inventory')
    exclusive(output/'execution_stdout.json',stdout)
    receipt={'passed':True,'pins_sha256':PINS_SHA256,'checker_sha256':CHECKER_SHA256,
             'science_root':str(science),'audit_root':str(audit),'output_root':str(output),
             'science_inventory_files':len(s_data),'audit_inventory_files':len(a_data),
             'golden_evidence_byte_equal':list(GOLDEN)+['run_stdout.json'],
             'fresh_actual_metadata_snapshots_byte_equal':True,
             'all_input_bytes_modes_mtimes_preserved':True,
             'checker_compile_optimize':0,'invoking_python_optimize':sys.flags.optimize,
             'executed':'Only authenticated unchanged independent_static_audit.py, using a release-only per-exec pathlib import facade',
             'inert':'Every science file (including author source, RULES44, and both proof dependencies); all other audit files',
             'limits':'Trusted Python and SymPy 1.14.0; quiescent POSIX filesystem. Path routing and input checks are not an OS/network sandbox; no hostile-runtime or concurrent-mutation safety claim.'}
    exclusive(output/'replay_receipt.json',(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode())
    print(json.dumps({'passed':True,'receipt':str(output/'replay_receipt.json')},sort_keys=True))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--science-root',required=True)
    parser.add_argument('--audit-root',required=True)
    parser.add_argument('--pins',required=True)
    parser.add_argument('--output-root',required=True)
    args=parser.parse_args()
    try:run(args)
    except Exception as exc:
        print('REJECTED: '+type(exc).__name__+': '+str(exc),file=sys.stderr)
        return 2
    return 0

if __name__=='__main__':raise SystemExit(main())
