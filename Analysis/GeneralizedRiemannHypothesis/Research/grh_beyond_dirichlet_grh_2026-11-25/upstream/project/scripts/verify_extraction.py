#!/usr/bin/env python3
"""Static integrity and local-import checks; this does not invoke Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tomllib


def stripped_lean(text):
    out = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif in_string:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1]); i += 2
            else:
                if text[i] == '"': in_string = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j == -1: out.extend(' ' * (len(text) - i)); break
            out.extend(' ' * (j - i)); i = j
        else:
            if text[i] == '"': in_string = True
            out.append(text[i]); i += 1
    if depth: raise ValueError('Unterminated block comment')
    return ''.join(out)


def imports(path):
    result = []
    for line in stripped_lean(path.read_text(encoding='utf-8')).splitlines():
        if re.match(r'^\s*import\s', line):
            for token in line.split()[1:]:
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', token):
                    raise ValueError(f'Unrecognized import token in {path}: {token}')
                result.append(token)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, help='Optional original Git checkout at the pinned revision')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / 'provenance.json').read_text())
    expected = {entry['path']: entry for entry in manifest['files']}
    if len(expected) != len(manifest['files']): raise ValueError('Duplicate manifest paths')
    for path, entry in expected.items():
        file = root / path
        if not file.is_file(): raise ValueError(f'Missing file: {path}')
        data = file.read_bytes()
        if len(data) != entry['size_bytes']: raise ValueError(f'Size mismatch: {path}')
        if hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError(f'SHA-256 mismatch: {path}')
        if entry['kind'] == 'unchanged_upstream':
            git_blob = hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()
            if git_blob != entry['upstream_git_blob_sha1']:
                raise ValueError(f'Git blob mismatch: {path}')

    source_modules = {entry['module']: root / path for path, entry in expected.items() if 'module' in entry}
    actual_sources = {p.relative_to(root).as_posix() for p in (root / 'src').rglob('*.lean')}
    expected_sources = {path for path in expected if path.startswith('src/') and path.endswith('.lean')}
    if actual_sources != expected_sources: raise ValueError('Added or missing Lean source files')
    graph = {module: imports(path) for module, path in source_modules.items()}
    if graph != manifest['import_graph']: raise ValueError('Import graph mismatch')

    def closure(target):
        seen = set()
        todo = [target]
        while todo:
            module = todo.pop()
            if module in seen: continue
            if module not in graph:
                if module.startswith(('Lib.', 'New.')):
                    raise ValueError(f'Missing local import: {module}')
                continue
            seen.add(module); todo.extend(graph[module])
        return seen

    closures = {target: closure(target) for target in manifest['target_modules']}
    union = set().union(*closures.values())
    if union != set(source_modules): raise ValueError('Not the exact local transitive closure')
    if len(union) != manifest['local_module_count']: raise ValueError('Module count mismatch')
    counts = {target: len(items) for target, items in closures.items()}
    if counts != manifest['per_target_local_closure_count_including_target']:
        raise ValueError('Per-target closure count mismatch')
    forbidden = set(manifest['omitted_endpoint_modules'])
    if union & forbidden: raise ValueError('Unexpected RH/GRH endpoint module')
    if any(name.startswith('New.Reduction.Zeros.') for name in union):
        raise ValueError('Unexpected zero-reduction module')
    external = sorted({imp for values in graph.values() for imp in values if imp not in graph})
    if external != manifest['external_imports']: raise ValueError('External imports mismatch')
    if imports(root / 'src/ExtractionAudit.lean') != manifest['target_modules']:
        raise ValueError('Audit imports differ from the selected targets')

    if (root / 'lean-toolchain').read_text().strip() != manifest['lean_toolchain']:
        raise ValueError('Lean toolchain mismatch')
    lake = tomllib.loads((root / 'lakefile.toml').read_text())
    if lake['defaultTargets'] != ['Lib', 'New', 'ExtractionAudit']:
        raise ValueError('Unexpected default Lake targets')
    requirements = {item['name']: item for item in lake['require']}
    if requirements['mathlib']['rev'] != manifest['mathlib_revision']:
        raise ValueError('Mathlib configuration revision mismatch')
    locked = json.loads((root / 'lake-manifest.json').read_text())
    mathlib = next(item for item in locked['packages'] if item['name'] == 'mathlib')
    if mathlib['rev'] != manifest['mathlib_revision']:
        raise ValueError('Mathlib lock-file revision mismatch')

    if args.upstream:
        upstream = args.upstream.resolve()
        head = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip()
        if head != manifest['upstream_commit']: raise ValueError(f'Wrong upstream HEAD: {head}')
        for path, entry in expected.items():
            if entry['kind'] != 'unchanged_upstream': continue
            original = upstream / entry['upstream_path']
            if original.read_bytes() != (root / path).read_bytes():
                raise ValueError(f'Upstream byte comparison failed: {path}')
            blob = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', f'{head}:{entry["upstream_path"]}'], text=True).strip()
            if blob != entry['upstream_git_blob_sha1']:
                raise ValueError(f'Pinned upstream Git blob differs: {path}')

    print(f'PASS: {len(expected)} packaged files passed SHA-256 and size checks.')
    print(f'PASS: exact closure of {len(union)} unchanged upstream Lean modules; external imports: {external}.')
    print('PASS: pinned Lean/Mathlib versions and no RH/GRH endpoint imports.')
    if args.upstream: print('PASS: all unchanged files match the pinned upstream Git checkout.')
    print('UNBUILT: these are static checks only; no Lean elaboration, build, or axiom audit was run.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        raise SystemExit(1)
