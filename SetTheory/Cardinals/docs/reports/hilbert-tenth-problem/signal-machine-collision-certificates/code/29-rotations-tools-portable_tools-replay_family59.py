#!/usr/bin/env python3
"""Relocated replay of authenticated, owned independent family59 checkers.

The two original checker byte streams are never edited. Their ROOT/OUT
assignments alone are redirected in an authenticated in-memory AST. Science
and upstream/Pell sources are only read as data. All input roots are explicit.
"""
import argparse
import ast
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

PACKET_MANIFEST_SHA = '646de47472089e9909fafbf0ed1e1a7851a114d862e4df9b31d0802815772044'
AUDIT_RECEIPT_SHA = '327ac64f5df5f8dbd2929cdcbabb147a19198bdf9b23291edb948b726514bbbe'
STATIC_CHECKER_SHA = '5b6b23ed6c65c9ce8089fd630e41961942477a61a4b8a685cf16e653cae9072a'
GEOMETRY_CHECKER_SHA = '4d15d07e5c4fbe706aecb829de09b21b8c3f643ab70d23254111783981650f4d'
DEPENDENCY_FILES = (
    '01-signal-map-obstruction-20261004-PROOF.md',
    '02-signal-dimension-boundary57-20261004-BOUNDARY_AND_ARITHMETIC.md',
    '03-five-signal-obstruction-independent-audit-20261004-INDEPENDENT_AUDIT.md',
    '04-five-signal-diophantine58-20261004-PROOF.md',
    '05-five-signal-family59-literature-20261004-SOURCE_COMPARISON.md',
    '06-five-signal-family59-arithmetic-review-20261004-ARITHMETIC_REVIEW.md',
    '07-sources-pell-source.lean',
)
EXPECTED_OUTPUTS = (
    'STATIC_INDEPENDENT_RECEIPT.json',
    'AUTHOR_PACKET_SNAPSHOT.json',
    'GEOMETRY_INDEPENDENT_RECEIPT.json',
    'DEPENDENCY_RECEIPT.json',
)

class ReplayError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise ReplayError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pairs_no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: '+key)
        result[key] = value
    return result

def parse_json(data):
    return json.loads(data.decode('utf-8'), object_pairs_hook=pairs_no_duplicates)

def regular_bytes(path):
    st = path.lstat()
    require(stat.S_ISREG(st.st_mode), 'not a regular file: '+str(path))
    return path.read_bytes()

def clean_relative(name):
    require(isinstance(name, str) and name, 'invalid relative path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and str(path) == name and
            all(part not in ('', '.', '..') for part in path.parts),
            'noncanonical relative path: '+repr(name))
    return path

def explicit_path(value, *, existing):
    # Reject symlink components rather than quietly resolving an alias.
    # Check before abspath: normalizing link/../root first would hide a link.
    require(bool(value), 'empty explicit path')
    require('..' not in Path(value).parts, 'parent traversal in explicit path: '+str(value))
    path = Path(os.path.abspath(value))
    current = Path(path.anchor)
    for part in path.parts[1:]:
        current = current/part
        if current.exists() or current.is_symlink():
            require(not current.is_symlink(), 'symlink path component: '+str(current))
    if existing:
        require(path.is_dir(), 'required input directory absent: '+str(path))
    else:
        require(not path.exists(), 'output must be a new absent directory: '+str(path))
        require(path.parent.is_dir(), 'output parent must already exist: '+str(path.parent))
    return path

def disjoint(paths):
    for i, left in enumerate(paths):
        for right in paths[i+1:]:
            require(left != right and left not in right.parents and right not in left.parents,
                    'input/output roots overlap: '+str(left)+' and '+str(right))

def inventory(root):
    result = {}
    for path in [root]+sorted(root.rglob('*')):
        st = path.lstat()
        require(not stat.S_ISLNK(st.st_mode), 'symlink in input inventory: '+str(path))
        rel = '.' if path == root else path.relative_to(root).as_posix()
        if stat.S_ISDIR(st.st_mode):
            result[rel] = {'kind':'directory','mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns}
        else:
            require(stat.S_ISREG(st.st_mode), 'special file in input inventory: '+str(path))
            result[rel] = {'kind':'file','mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,
                           'bytes':st.st_size,'sha256':sha(path.read_bytes())}
    return result

def authenticate_tree(root, expected):
    actual = inventory(root)
    dirs = {'.'}
    for name in expected:
        path = clean_relative(name)
        dirs.update(str(p) for p in path.parents if str(p) != '.')
    require(set(actual) == set(expected)|dirs, 'complete inventory mismatch at '+str(root))
    for name, expected_record in expected.items():
        record = actual[name]
        require(record['kind'] == 'file' and record['sha256'] == expected_record['sha256'],
                'file authentication failed: '+str(root/name))
        if 'bytes' in expected_record:
            require(record['bytes'] == expected_record['bytes'], 'file size mismatch: '+name)
    return actual

def manifest_records(entries):
    result = {}
    for entry in entries:
        require(set(entry) == {'path','bytes','sha256'}, 'unexpected manifest schema')
        name = str(clean_relative(entry['path']))
        require(name not in result, 'duplicate manifest path: '+name)
        result[name] = {'bytes':entry['bytes'],'sha256':entry['sha256']}
    return result

def redirect_owned_checker(source, expected_sha, packet, output, is_static):
    data = regular_bytes(source)
    require(sha(data) == expected_sha, 'owned checker hash mismatch')
    tree = ast.parse(data.decode('utf-8'), filename=str(source))
    routes = {'OUT':output}
    if is_static:
        routes['ROOT'] = packet
    original_values = {
        # This string is checked as inert AST data and is never a fallback path.
        'ROOT': "Path('/workspace/shared/five-signal-rotation-family59-20261004')",
        'OUT': 'Path(__file__).resolve().parent',
    }
    count = {name:0 for name in routes}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in routes:
                old = ast.parse(original_values[name], mode='eval').body
                require(ast.dump(node.value) == ast.dump(old), 'unexpected route assignment: '+name)
                node.value = ast.Call(func=ast.Name(id='Path',ctx=ast.Load()),
                                      args=[ast.Constant(value=str(routes[name]))],keywords=[])
                count[name] += 1
    require(all(value == 1 for value in count.values()), 'route assignment count mismatch')
    ast.fix_missing_locations(tree)
    # Explicit optimize=0 retains the frozen checkers' assertions even under -O.
    return compile(tree, str(source), 'exec', dont_inherit=True, optimize=0), count

def replay(packet, audit, dependencies, output):
    sys.dont_write_bytecode = True
    disjoint((packet,audit,dependencies,output))
    manifest_data = regular_bytes(packet/'PACKET_MANIFEST.json')
    require(sha(manifest_data) == PACKET_MANIFEST_SHA, 'packet manifest trust-anchor mismatch')
    manifest = parse_json(manifest_data)
    expected_packet = manifest_records(manifest['files'])
    expected_packet['PACKET_MANIFEST.json'] = {'bytes':len(manifest_data),'sha256':PACKET_MANIFEST_SHA}
    packet_before = authenticate_tree(packet, expected_packet)

    receipt_data = regular_bytes(audit/'AUDIT_RECEIPT.json')
    require(sha(receipt_data) == AUDIT_RECEIPT_SHA, 'audit receipt trust-anchor mismatch')
    receipt = parse_json(receipt_data)
    expected_audit = dict(receipt['audit_files'])
    expected_audit['AUDIT_RECEIPT.json'] = {'bytes':len(receipt_data),'sha256':AUDIT_RECEIPT_SHA}
    audit_before = authenticate_tree(audit, expected_audit)

    pins = parse_json(regular_bytes(packet/'SOURCE_PINS.json'))['read_only_dependencies']
    require(len(pins) == len(DEPENDENCY_FILES), 'dependency mapping length mismatch')
    expected_deps = {name:{'sha256':pin['sha256']} for name,pin in zip(DEPENDENCY_FILES,pins)}
    deps_before = authenticate_tree(dependencies, expected_deps)
    dependency_rows = []
    for name, pin in zip(DEPENDENCY_FILES,pins):
        digest = deps_before[name]['sha256']
        dependency_rows.append({**pin,'actual_sha256':digest,'verified':True})
    dependency_receipt = {'status':'PASS','dependencies':dependency_rows,'mode':'inert text/hash reads only'}
    dependency_bytes = (json.dumps(dependency_receipt,indent=2)+'\n').encode()
    require(dependency_bytes == regular_bytes(audit/'DEPENDENCY_RECEIPT.json'),
            'dependency receipt would not reproduce exactly')

    code_static, routes_static = redirect_owned_checker(audit/'audit_static.py', STATIC_CHECKER_SHA, packet, output, True)
    code_geometry, routes_geometry = redirect_owned_checker(audit/'audit_geometry.py', GEOMETRY_CHECKER_SHA, packet, output, False)
    # Dependency availability is checked before creating any output directory.
    import sympy
    output.mkdir(mode=0o700)
    for source, code in [('audit_static.py',code_static),('audit_geometry.py',code_geometry)]:
        with contextlib.redirect_stdout(io.StringIO()):
            exec(code, {'__name__':'__main__','__file__':str(audit/source)})
    (output/'DEPENDENCY_RECEIPT.json').write_bytes(dependency_bytes)
    require({p.name for p in output.iterdir()} == set(EXPECTED_OUTPUTS), 'unexpected replay output inventory')
    output_hashes = {}
    for name in EXPECTED_OUTPUTS:
        regenerated = regular_bytes(output/name)
        require(regenerated == regular_bytes(audit/name), 'regenerated output differs byte-for-byte: '+name)
        output_hashes[name] = sha(regenerated)
    for root, before in ((packet,packet_before),(audit,audit_before),(dependencies,deps_before)):
        require(inventory(root) == before, 'input bytes or metadata changed: '+str(root))
    result = {
        'status':'PASS',
        'scope':'authenticated relocated replay of owned independent checkers; science/upstream files inert',
        'packet_manifest_sha256':PACKET_MANIFEST_SHA,
        'audit_receipt_sha256':AUDIT_RECEIPT_SHA,
        'packet_files':len(expected_packet),'audit_files':len(expected_audit),'dependency_files':len(expected_deps),
        'in_memory_route_assignments':{'audit_static.py':routes_static,'audit_geometry.py':routes_geometry},
        'byte_identical_outputs':output_hashes,
        'input_bytes_modes_mtimes_preserved':True,
        'historical_path_fallback':False,
        'author_constructor_or_upstream_execution':False,
    }
    (output/'REPLAY_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',required=True,help='exact frozen 60-file science packet directory')
    parser.add_argument('--audit',required=True,help='exact frozen 9-file independent-audit directory')
    parser.add_argument('--dependencies',required=True,help='exact seven-file relocated dependency directory')
    parser.add_argument('--output',required=True,help='new absent output directory; parent must exist')
    args = parser.parse_args(argv)
    try:
        paths = [explicit_path(getattr(args,k),existing=k!='output') for k in ('packet','audit','dependencies','output')]
        result = replay(*paths)
    except Exception as error:
        print('family59 replay FAILED: '+str(error),file=sys.stderr)
        return 1
    print(json.dumps(result,indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
