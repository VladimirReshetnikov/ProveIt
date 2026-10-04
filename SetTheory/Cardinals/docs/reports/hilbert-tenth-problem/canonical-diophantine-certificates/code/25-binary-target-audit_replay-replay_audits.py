#!/usr/bin/env python3
"""Portable path-only replay of two frozen independently authored checks.

Authenticated checker bytes are compiled directly, without bytecode caches.
Only their filesystem globals are redirected. Their original, unmodified main
bodies perform all tests and construct their own receipts. Submitted science
programs are read as data only; none is imported or executed.
"""
import sys
if sys.flags.optimize != 0 or not __debug__:
    raise SystemExit("Replay refused or failed: Optimized Python is forbidden: scientific assertions must run")
if sys.flags.isolated != 1:
    raise SystemExit("Replay refused or failed: Isolated Python is required; invoke with python -I")

import argparse
import ast
import contextlib
import hashlib
import json
import os
from pathlib import Path
import stat
import types

AUDIT_MANIFEST_SHA256 = 'dd6a27229d204f993b36e3f74a794353fa925e34926fd60fa3974eb1c50a33ab'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(raw, exists):
    original = Path(raw)
    require('..' not in original.parts, 'Parent traversal is forbidden')
    path = Path(os.path.abspath(original))
    cursor = Path(path.anchor)
    for component in path.parts[1:]:
        cursor /= component
        try:
            info = cursor.lstat()
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(info.st_mode), 'Symlink path component rejected: '+str(cursor))
    if exists:
        require(path.exists(), 'Required path missing: '+str(path))
    return path


def inside(child, parent):
    try:
        child.relative_to(parent)
        return True
    except ValueError:
        return False


def disjoint(a,b): return not inside(a,b) and not inside(b,a)


def snapshot(root):
    require(root.is_dir(), 'Input root must be a directory: '+str(root))
    result = {}
    for path in [root, *sorted(root.rglob('*'))]:
        info = path.lstat()
        require(not stat.S_ISLNK(info.st_mode), 'Symlink input rejected: '+str(path))
        record = {'mode':info.st_mode, 'mtime_ns':info.st_mtime_ns}
        if stat.S_ISREG(info.st_mode):
            record.update(bytes=info.st_size, sha256=digest(path))
        else:
            require(stat.S_ISDIR(info.st_mode), 'Nonregular input rejected: '+str(path))
        result[str(path.relative_to(root))] = record
    return result


def pinned_child(root, name):
    relative = Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe pinned child path')
    path = safe_path(root/relative, True)
    require(path.is_file(), 'Pinned child must be a regular file: '+str(path))
    return path


def original_main_body(tree):
    def is_main_guard(node):
        test = node.test if isinstance(node,ast.If) else None
        return isinstance(test,ast.Compare) and isinstance(test.left,ast.Name) and test.left.id=='__name__' and \
            len(test.ops)==1 and isinstance(test.ops[0],ast.Eq) and len(test.comparators)==1 and \
            isinstance(test.comparators[0],ast.Constant) and test.comparators[0].value=='__main__'
    guards = [node for node in tree.body if is_main_guard(node)]
    require(len(guards)==1 and tree.body[-1] is guards[0] and not guards[0].orelse,
        'Pinned checker must have exactly one final ordinary main guard')
    # AST nodes are the original statements, not rewritten or replaced.
    return ast.Module(body=guards[0].body, type_ignores=[])


def run_frozen(checker, redirects, log):
    frozen = checker.read_bytes()
    tree = ast.parse(frozen, filename=str(checker))
    entry = original_main_body(tree)
    module = types.ModuleType('authenticated_frozen_'+checker.stem)
    module.__file__ = str(checker)
    old = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        # The module name is not __main__, so the unchanged guard does not run.
        exec(compile(frozen,str(checker),'exec',dont_inherit=True,optimize=0),module.__dict__)
        for name,path in redirects.items():
            require(name in module.__dict__ and isinstance(module.__dict__[name],Path),
                'Expected filesystem global is missing: '+name)
            module.__dict__[name]=path
        with log.open('w') as stream, contextlib.redirect_stdout(stream):
            # Run exactly the original terminal body, including its own receipt
            # construction and self-hash. Only the path globals differ.
            exec(compile(entry,str(checker),'exec',dont_inherit=True,optimize=0),module.__dict__)
    finally:
        sys.dont_write_bytecode = old
    require(checker.read_bytes()==frozen, 'Frozen checker bytes changed')


def main():
    require(sys.flags.optimize==0 and __debug__, 'Optimized Python is forbidden: scientific assertions must run')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',required=True,help='Frozen target certificate directory')
    parser.add_argument('--audit-root',required=True,help='Frozen independent audit directory')
    parser.add_argument('--output',required=True,help='New disjoint directory; parent must exist')
    args=parser.parse_args()
    source,audit= safe_path(args.source_root,True),safe_path(args.audit_root,True)
    output=safe_path(args.output,False)
    runner=safe_path(__file__,True)
    require(source.is_dir() and audit.is_dir(), 'Both input roots must be directories')
    require(disjoint(source,audit), 'Source and audit roots must not overlap')
    for root in [source,audit,runner.parent]:
        require(disjoint(output,root), 'Output must not overlap source, audit, or adapter root')
    require(not output.exists(), 'Output already exists; use a fresh directory')
    require(output.parent.is_dir(), 'Output parent must already exist')
    before={'source':snapshot(source),'audit':snapshot(audit)}
    runner_before=digest(runner)
    manifest_path=pinned_child(audit,'audit-manifest.json')
    require(digest(manifest_path)==AUDIT_MANIFEST_SHA256, 'Frozen audit manifest hash mismatch')
    manifest=json.loads(manifest_path.read_text())
    for group,root in [('source_files',source),('audit_files',audit)]:
        for name,pin in manifest[group].items():
            path=pinned_child(root,name)
            require(path.stat().st_size==pin['bytes'] and digest(path)==pin['sha256'],
                'Frozen input pin mismatch: '+group+'/'+name)
    main_checker=pinned_child(audit,'independent_check.py')
    semantic_checker=pinned_child(audit,'semantics_check.py')
    expected_main=pinned_child(audit,'audit-receipt.json').read_bytes()
    expected_log=pinned_child(audit,'audit-run.log').read_bytes()
    expected_semantics=pinned_child(audit,'semantics-receipt.json').read_bytes()
    output.mkdir(mode=0o700)
    try:
        run_frozen(main_checker, {'SOURCE':source,'HERE':output}, output/'audit-run.log')
        run_frozen(semantic_checker, {'ROOT':output}, output/'semantics-run.log')
        require((output/'audit-receipt.json').read_bytes()==expected_main, 'Main scientific receipt changed')
        require((output/'audit-run.log').read_bytes()==expected_log, 'Main scientific log changed')
        require((output/'semantics-receipt.json').read_bytes()==expected_semantics, 'Semantic scientific receipt changed')
        require((output/'semantics-run.log').read_bytes()==expected_semantics, 'Semantic scientific log changed')
    finally:
        after={'source':snapshot(source),'audit':snapshot(audit)}
        require(before==after, 'Frozen input tree, bytes, modes, or mtimes changed')
        require(digest(runner)==runner_before, 'Adapter bytes changed during replay')
    result={
        'status':'PASS', 'adapter_kind':'Only SOURCE/HERE/ROOT filesystem globals redirected; original main bodies unchanged',
        'audit_manifest_sha256':AUDIT_MANIFEST_SHA256,
        'main_checker_sha256':digest(main_checker), 'semantic_checker_sha256':digest(semantic_checker),
        'main_receipt_sha256':digest(output/'audit-receipt.json'),
        'semantic_receipt_sha256':digest(output/'semantics-receipt.json'),
        'main_log_sha256':digest(output/'audit-run.log'), 'semantic_log_sha256':digest(output/'semantics-run.log'),
        'adapter_sha256':runner_before, 'main_receipt_byte_identical':True, 'main_log_byte_identical':True,
        'semantic_receipt_byte_identical':True, 'semantic_log_byte_identical':True,
        'frozen_input_tree_bytes_modes_mtimes_preserved':True, 'submitted_executables_run':False,
        'optimized_python_rejected':True}
    (output/'replay-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        print('Replay refused or failed: '+str(error),file=sys.stderr)
        sys.exit(1)
