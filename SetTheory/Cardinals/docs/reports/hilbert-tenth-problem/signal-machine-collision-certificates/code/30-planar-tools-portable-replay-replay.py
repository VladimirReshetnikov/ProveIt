#!/usr/bin/env python3
"""Replay only frozen independently owned Report60 checkers at explicit roots."""
import argparse
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import sys
import sysconfig

sys.dont_write_bytecode = True
PINS_SHA256 = 'c9794e791685c5a03e87d15a2b3bb0727847372b38fb067b3c8f7d64da1a3818'
ROLES = ('physical_science', 'geometry_science', 'arithmetic_science', 'quadratic_science',
         'physical_audit', 'geometry_audit', 'arithmetic_audit', 'quadratic_audit', 'dependencies')


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical_path(raw, *, existing):
    p = Path(raw)
    require(p.is_absolute(), 'Every input and output path must be explicit and absolute')
    require('..' not in p.parts and '.' not in p.parts, 'Dot path components are forbidden')
    resolved = p.resolve(strict=existing)
    require(str(raw) == str(resolved), 'A root must be canonical: no symlink or normalized alias')
    current = p if existing else p.parent
    while True:
        require(not current.is_symlink(), 'Symlink path component is forbidden')
        if current == current.parent:
            break
        current = current.parent
    if existing:
        require(p.is_dir(), 'Input root must be a directory: '+str(p))
    return p


def inside(path, root):
    return path == root or root in path.parents


def inventory(root):
    rows = []
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat()
        require(not stat.S_ISLNK(s.st_mode), 'Symlink entry is forbidden: '+str(p))
        require(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode), 'Nonregular entry is forbidden: '+str(p))
        is_file = stat.S_ISREG(s.st_mode)
        if is_file:
            require(s.st_nlink == 1, 'Hardlinked file is forbidden: '+str(p))
        row = {'path':'.' if p == root else p.relative_to(root).as_posix(),
               'kind':'file' if is_file else 'directory',
               'mode':stat.S_IMODE(s.st_mode), 'mtime_ns':s.st_mtime_ns,
               'size':s.st_size, 'nlink':s.st_nlink}
        if is_file:
            row['sha256'] = sha(p.read_bytes())
        rows.append(row)
    return rows


def content_inventory(rows):
    return [{'path':r['path'], 'kind':r['kind'],
             **({'size':r['size'], 'sha256':r['sha256']} if r['kind']=='file' else {})}
            for r in rows]


def authenticate(root, expected):
    observed = inventory(root)
    require(content_inventory(observed) == expected, 'Authenticated tree mismatch: '+str(root))
    return observed


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')


def physical_runtime_baseline(root):
    # Matches the unchanged physical checker's runtime preservation format.
    records=[]
    for p in sorted(root.rglob('*')):
        s=p.stat()
        records.append({'path':str(p.relative_to(root)), 'mode':stat.S_IMODE(s.st_mode),
                        'mtime_ns':s.st_mtime_ns, 'size':s.st_size, 'is_file':p.is_file(),
                        **({'sha256':sha(p.read_bytes())} if p.is_file() else {})})
    return records


class ReadWriteGuard:
    """Reject checker access outside supplied inputs, Python libraries, and output.

    This supplements pinned-code review; it is not a sandbox for hostile Python.
    In particular no historical provenance string becomes an allowed root.
    """
    def __init__(self, read_roots, protected_roots, output):
        self.read_roots=tuple(read_roots)
        self.protected_roots=tuple(protected_roots)
        self.output=output
        self.active=True
    def path(self, value):
        require(isinstance(value,(str,bytes,os.PathLike)), 'Unapproved descriptor-based file access')
        p=Path(os.fsdecode(value))
        require(p.is_absolute(), 'Checker relative filesystem access is forbidden')
        return p.resolve(strict=False)
    def check(self, value, writing=False):
        p=self.path(value)
        if writing:
            if any(inside(p,r) for r in self.protected_roots):
                raise PermissionError('Checker write to protected input denied: '+str(p))
            if not inside(p,self.output):
                raise PermissionError('Checker write outside fresh output denied: '+str(p))
        elif not any(inside(p,r) for r in self.read_roots):
            raise PermissionError('Checker read outside explicit roots denied: '+str(p))
    def __call__(self,event,args):
        if not self.active:
            return
        if event=='open':
            path,mode,flags=args
            writing=bool(flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND))
            if isinstance(mode,str):
                writing=writing or any(c in mode for c in 'wax+')
            self.check(path,writing)
        elif event in ('os.listdir','os.scandir'):
            self.check(args[0])
        elif event in ('os.mkdir','os.remove','os.rmdir','os.chmod','os.utime','os.truncate'):
            self.check(args[0],True)
        elif event in ('os.rename','os.link','os.symlink'):
            raise PermissionError('Checker rename/link operations are forbidden')
        elif event in ('subprocess.Popen','os.system','os.exec','os.posix_spawn') or event.startswith('socket.'):
            raise PermissionError('Checker process/network operations are forbidden')


def inspected_namespace(path, wanted_hash, *, main=False):
    raw=path.read_bytes()
    require(sha(raw)==wanted_hash,'Owned checker changed before execution')
    ns={'__name__':'__main__' if main else '__portable_owned_checker__',
        '__file__':str(path), '__package__':None}
    # optimize=0 deliberately retains every independent assertion even if the
    # release wrapper itself was launched with python -O.
    exec(compile(raw,str(path),'exec',dont_inherit=True,optimize=0),ns)
    return ns


def compare_file(actual, expected, comparisons):
    observed=actual.read_bytes()
    wanted=expected.read_bytes()
    require(observed==wanted,'Byte-for-byte expected-output mismatch: '+str(actual))
    comparisons.append({'output':str(actual), 'expected':str(expected),
                        'bytes':len(observed),'sha256':sha(observed),'byte_identical':True})


def run_physical(roots, output, checker, comparisons):
    where=output/'physical'; where.mkdir()
    write_json(where/'frozen_inventory_before.json',physical_runtime_baseline(roots['physical_science']))
    capture=io.StringIO()
    with contextlib.redirect_stdout(capture):
        ns=inspected_namespace(roots['physical_audit']/checker['file'],checker['sha256'])
        # Only runtime root bindings are changed. The frozen source is compiled
        # verbatim, and its own source hash continues to identify those bytes.
        ns['SRC']=roots['physical_science']; ns['OUT']=where
        ns['main']()
    (where/'run_stdout.json').write_bytes(capture.getvalue().encode('utf-8'))
    compare_file(where/'independent_results.json',roots['physical_audit']/'independent_results.json',comparisons)
    compare_file(where/'run_stdout.json',roots['physical_audit']/'run_stdout.json',comparisons)
    require((where/'frozen_inventory_before.json').read_bytes()==(where/'frozen_inventory_after.json').read_bytes(),
            'Physical checker runtime preservation failed')


def run_geometry(roots, output, checker, comparisons):
    where=output/'geometry'; where.mkdir()
    capture=io.StringIO()
    with contextlib.redirect_stdout(capture):
        inspected_namespace(roots['geometry_audit']/checker['file'],checker['sha256'],main=True)
    path=where/'independent_results.json'
    path.write_bytes(capture.getvalue().encode('utf-8'))
    compare_file(path,roots['geometry_audit']/'independent_results.json',comparisons)
    compare_file(path,roots['geometry_audit']/'independent_results_optimized.json',comparisons)


def run_arithmetic(roots, output, family, checker, comparisons):
    where=output/'arithmetic'  # The owned checker itself requires a new directory.
    argv=[str(roots['arithmetic_audit']/checker['file']),
          '--certificate-root',str(roots['arithmetic_science']),
          '--classification-root',str(roots['geometry_science']),
          '--physical-root',str(roots['physical_science']),
          '--family59-root',str(family),
          '--source-manifest',str(roots['arithmetic_audit']/'SOURCE_SNAPSHOT_BEFORE.json'),
          '--output',str(where)]
    capture=io.StringIO(); previous=sys.argv
    try:
        sys.argv=argv
        with contextlib.redirect_stdout(capture):
            ns=inspected_namespace(roots['arithmetic_audit']/checker['file'],checker['sha256'])
            ns['main']()
    finally:
        sys.argv=previous
    (where/'AUDIT_RUN.txt').write_bytes(capture.getvalue().encode('utf-8'))
    for filename in ('EXACT_RECEIPT.json','RECONSTRUCTED_SCHEMAS.json','AUDIT_RUN.txt'):
        compare_file(where/filename,roots['arithmetic_audit']/filename,comparisons)
    require((where/'OBSERVED_SOURCES_BEFORE.json').read_bytes()==(where/'OBSERVED_SOURCES_AFTER.json').read_bytes(),
            'Arithmetic checker runtime preservation failed')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for role in ROLES:
        parser.add_argument('--'+role.replace('_','-')+'-root',required=True)
    parser.add_argument('--release-root',required=True)
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    adapter_source=Path(__file__)
    require(adapter_source.is_absolute() and str(adapter_source)==str(adapter_source.resolve(strict=True)),
            'Adapter source must be canonical with no symlink path components')
    adapter=adapter_source.parent
    pins_path=adapter/'INPUT_PINS.json'
    raw=pins_path.read_bytes()
    require(sha(raw)==PINS_SHA256,'Immutable input-pins digest mismatch')
    pins=json.loads(raw)
    roots={role:canonical_path(getattr(args,role+'_root'),existing=True) for role in ROLES}
    release=canonical_path(args.release_root,existing=True)
    require(all(root!=release and inside(root,release) for root in roots.values()),
            'Every scientific, audit, and dependency root must be a strict descendant of the explicit release root')
    selected=list(roots.values())+[adapter]
    for i,left in enumerate(selected):
        for right in selected[i+1:]:
            require(not inside(left,right) and not inside(right,left),'Input roots must be disjoint')
    output=canonical_path(args.output,existing=False)
    require(not output.exists() and not output.is_symlink(),'Output must be fresh and nonexistent')
    require(output.parent.is_dir(),'Output parent must already exist')
    for root in selected+[release]:
        require(not inside(output,root) and not inside(root,output),'Output must be external to every input root')
    before={role:authenticate(roots[role],pins['trees'][role]) for role in ROLES}
    before['adapter']=inventory(adapter)
    before['release']=inventory(release)
    # Pin the runtime engine before executing any owned checker.
    import sympy
    import mpmath
    require(sympy.__version__==pins['sympy_version'],'Pinned SymPy version is required')
    output.mkdir()
    write_json(output/'INPUT_INVENTORY_BEFORE.json',before)
    # Arithmetic's two old-family dependencies get a read-only logical view.
    # These are authenticated byte copies, never hardlinks or symlinks.
    family=output/'family59_source_view'; (family/'inert_sources').mkdir(parents=True)
    for source,dest in [('report59-proof.md','PROOF.md'),('pell-source.lean','inert_sources/pell-source.lean')]:
        target=family/dest
        target.write_bytes((roots['dependencies']/source).read_bytes())
        target.chmod(0o444)
    (family/'inert_sources').chmod(0o555); family.chmod(0o555)
    family_before=inventory(family)
    write_json(output/'FAMILY59_VIEW_BEFORE.json',family_before)
    libraries={Path(sysconfig.get_path(name)).resolve()
               for name in ('stdlib','platstdlib','purelib','platlib')}
    libraries.update((Path(sympy.__file__).resolve().parent,Path(mpmath.__file__).resolve().parent))
    protected=selected+[release,family]+list(libraries)
    guard=ReadWriteGuard(selected+[family]+list(libraries)+[output],protected,output)
    sys.addaudithook(guard)
    comparisons=[]
    run_physical(roots,output,pins['checkers']['physical'],comparisons)
    run_geometry(roots,output,pins['checkers']['geometry'],comparisons)
    run_arithmetic(roots,output,family,pins['checkers']['arithmetic'],comparisons)
    guard.active=False  # Only the adapter's full-release preservation scan follows.
    after={role:inventory(roots[role]) for role in ROLES}
    after['adapter']=inventory(adapter)
    after['release']=inventory(release)
    require(after==before,'An input tree changed in bytes, inventory, mode, mtime, size, or link count')
    write_json(output/'INPUT_INVENTORY_AFTER.json',after)
    require(inventory(family)==family_before,'Read-only dependency view changed')
    write_json(output/'FAMILY59_VIEW_AFTER.json',inventory(family))
    receipt={'status':'PASS','input_pins_sha256':PINS_SHA256,
             'explicit_roots':{k:str(v) for k,v in roots.items()},
             'release_root':str(release),
             'output':str(output),'owned_checkers':pins['checkers'],
             'source_bytes_modes_mtimes_inventory_unchanged':True,
             'all_owned_code_compiled_with_optimize_zero':True,
             'no_author_science_programs_executed':True,
             'inert_authenticated_roles':['quadratic_science','quadratic_audit'],
             'quadratic_independent_executable_replay_claimed':False,
             'no_historical_root_fallback':True,
             'comparisons':comparisons}
    write_json(output/'REPLAY_RECEIPT.json',receipt)
    write_json(output/'OUTPUT_INVENTORY.json',inventory(output))
    print(json.dumps({'status':'PASS','output':str(output),'byte_comparisons':len(comparisons),
                      'receipt_sha256':sha((output/'REPLAY_RECEIPT.json').read_bytes())},indent=2))


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        print(type(error).__name__+': '+str(error),file=sys.stderr)
        raise SystemExit(1)
