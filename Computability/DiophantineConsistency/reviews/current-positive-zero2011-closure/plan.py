#!/usr/bin/env python3
"""Read-only source/object inventory; never invokes Lean or writes project files."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tomllib

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
RUN = Path(__file__).resolve().parent
HEAD = '09eaa57ae5b80130ddb0aa5344f71e638ebb3e97'
BASE = 'c77fd6aca2a05e4da34a2b87d5f41a27666db316'
TARGETS = ['DiophantineConsistency.CurrentPositiveZero2011',
           'DiophantineConsistency.CurrentPositiveZero2011Checks']
REVIEWS = ROOT / 'Computability/DiophantineConsistency/reviews'
SHARED = ROOT / '.lake/build/lib/lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()

def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()

def file_record(path):
    path = Path(path)
    return {'path': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size}

def uncomment(text):
    # Preserve line boundaries, nested comments, and quoted strings. Imports are
    # read only from the initial header, so text inside declaration strings is inert.
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i+1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if text[i] == '"': quoted = False
                i += 1
        elif pair == '/-': depth = 1; out.append(' '); i += 2
        elif pair == '--':
            while i < len(text) and text[i] != '\n': i += 1
        else:
            quoted = text[i] == '"'
            out.append(text[i]); i += 1
    require(depth == 0, 'Unclosed comment')
    return ''.join(out)

def imports(source):
    lines = uncomment(source.read_text()).splitlines()
    result, header, prelude = [], True, False
    for raw in lines:
        line = raw.strip()
        if not line: continue
        if header and line in ('module', 'prelude'):
            prelude |= line == 'prelude'; continue
        match = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)', line)
        if match:
            require(header, 'Import after declarations in ' + str(source))
            names = match.group(1).split()
            require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names),
                    'Unsupported import syntax: ' + line)
            result.extend(names)
        else:
            header = False
    if not prelude and 'Init' not in result: result.insert(0, 'Init')
    return list(dict.fromkeys(result))

def main():
    # Later documentation-only commits are harmless: every selected source is
    # checked below against this exact approved source snapshot.
    subprocess.run(['git','merge-base','--is-ancestor',HEAD,'HEAD'], cwd=ROOT, check=True)
    roots = {x['name']: x.get('srcDir', '.') for x in
             tomllib.loads((ROOT / 'lakefile.toml').read_text())['lean_lib']}
    lean_path = command('lake', 'env', 'printenv', 'LEAN_PATH').split(os.pathsep)
    external_paths = [p for p in lean_path if Path(p).resolve() != SHARED.resolve()]
    require(len(external_paths) + 1 == len(lean_path), 'Expected one shared project path')
    evidence_paths = [REVIEWS / 'machine215-current-closure-completed.json',
                      Path('/tmp/diophantine-bridge-identical-cache-receipt.json')]
    machine = json.loads(evidence_paths[0].read_text())
    require(machine['compiler_sha256'] == sha(LEAN), 'Compiler differs from machine receipt')
    require(machine['Init_sha256'] == sha(LEAN.parent.parent/'lib/lean/Init.olean'),
            'Init differs from machine receipt')
    evidence = {x['module']: {'source_sha256': x['source_sha256'],
                'object_sha256': x['current_object_sha256'],
                'receipt': str(evidence_paths[0]), 'origin': x['driver_origin']}
                for x in machine['modules']}
    bridge = json.loads(evidence_paths[1].read_text())
    bridge_sources = {x['module']: x for x in bridge['closure']}
    for x in bridge['copied']:
        name = x['module']
        primary = next(v for v in x['objects'] if v['path'].endswith('.olean'))
        evidence[name] = {'source_sha256': bridge_sources[name]['source_sha256'],
            'object_sha256': primary['sha256'], 'receipt': str(evidence_paths[1]),
            'origin': 'exact_source_bridge_cache'}
    modules, external, visiting = {}, {}, set()
    def visit(name):
        if name in modules or name in external: return
        root = name.split('.')[0]
        rel = Path(*name.split('.')).with_suffix('.lean')
        if root not in roots:
            obj = next((Path(p)/rel.with_suffix('.olean') for p in external_paths
                        if (Path(p)/rel.with_suffix('.olean')).is_file()), None)
            require(obj is not None, 'Missing external boundary object: ' + name)
            companions = [file_record(Path(str(obj)+s)) for s in ('.private','.server')
                          if Path(str(obj)+s).is_file()]
            prefix, marker, tail = str(obj).partition('/.lake/build/lib/lean/')
            source = (Path(prefix)/Path(tail).with_suffix('.lean') if marker else
                      LEAN.parent.parent/'src/lean'/rel)
            external[name] = {'module': name, 'object': file_record(obj),
                'companions': companions,
                'observed_source': file_record(source) if source.is_file() else None}
            return
        require(name not in visiting, 'Import cycle at ' + name)
        visiting.add(name)
        source = ROOT / roots[root] / rel
        require(source.is_file(), 'Missing custom source: ' + str(source))
        source_sha = sha(source)
        git_source = subprocess.check_output(['git', 'show', HEAD+':'+str(source.relative_to(ROOT))], cwd=ROOT)
        require(hashlib.sha256(git_source).hexdigest() == source_sha,
                'Source is not the exact committed snapshot: ' + name)
        deps = imports(source)
        for dep in deps: visit(dep)
        visiting.remove(name)
        obj = SHARED / rel.with_suffix('.olean')
        current = file_record(obj) if obj.is_file() else None
        ev = evidence.get(name)
        source_match = ev is not None and ev['source_sha256'] == source_sha
        object_match = ev is not None and current is not None and ev['object_sha256'] == current['sha256']
        authenticated = source_match and object_match
        invalid_deps = [d for d in deps if d in modules and modules[d]['action'] == 'fresh']
        reuse = authenticated and not invalid_deps and name not in TARGETS
        reason = ('authenticated_closed_cache' if reuse else
                  'target_forced_fresh' if name in TARGETS else
                  'dependency_requires_fresh' if authenticated and invalid_deps else
                  'missing_object' if current is None else
                  'source_receipt_mismatch' if ev and not source_match else
                  'object_receipt_mismatch' if ev and not object_match else
                  'no_selected_source_object_receipt')
        companions = [file_record(Path(str(obj)+s)) for s in ('.private', '.server')
                      if Path(str(obj)+s).is_file()]
        modules[name] = {'module': name, 'source': file_record(source),
            'imports': deps, 'observed_shared_object': current,
            'observed_companions': companions, 'evidence': ev,
            'source_receipt_matches': source_match, 'object_receipt_matches': object_match,
            'action': 'reuse' if reuse else 'fresh', 'reason': reason,
            'fresh_dependencies': invalid_deps}
    for target in TARGETS: visit(target)
    changed_paths = set(command('git', 'diff', '--name-only', BASE, HEAD).splitlines())
    changed = [n for n,x in modules.items() if str(Path(x['source']['path']).relative_to(ROOT)) in changed_paths]
    modified_paths = set(command('git','diff','--name-only','--diff-filter=M',BASE,HEAD).splitlines())
    modified = [n for n,x in modules.items() if str(Path(x['source']['path']).relative_to(ROOT)) in modified_paths]
    affected = set(changed)
    for n,x in modules.items():
        if any(d in affected for d in x['imports']): affected.add(n)
    fresh = [x for x in modules.values() if x['action'] == 'fresh']
    manifest = {'status': 'PLAN_ONLY_NOT_EXECUTED', 'root': str(ROOT), 'head': HEAD,
        'comparison_base': BASE, 'targets': TARGETS, 'external_lean_path': external_paths,
        'toolchain': [file_record(ROOT/p) for p in ('lean-toolchain','lakefile.toml','lake-manifest.json')]
          + [file_record(LEAN),file_record(LEAN.parent.parent/'lib/lean/Init.olean')],
        'evidence_files': [file_record(p) for p in evidence_paths],
        'modules': list(modules.values()), 'external_boundary': list(external.values()),
        'changed_custom_modules_since_comparison': changed,
        'modified_existing_custom_modules_since_comparison': modified,
        'changed_or_dependent_custom_modules': sorted(affected),
        'summary': {'custom_modules': len(modules), 'reuse': len(modules)-len(fresh),
            'fresh': len(fresh), 'external_direct_imports': len(external),
            'missing_custom_objects': sum(x['observed_shared_object'] is None for x in fresh),
            'fresh_observed_primary_bytes': sum(x['observed_shared_object']['bytes']
                    for x in fresh if x['observed_shared_object']),
            'changed_sources': len(changed), 'affected_nodes': len(affected)},
        'cache_boundary': 'Only the selected machine/Bridge receipts authenticate reuse. Other receipts have not been exhaustively harvested. All other custom modules are conservatively fresh.',
        'external_boundary_scope': 'Installed package/toolchain objects are a trusted precompiled boundary, not source-replayed. Direct boundary objects are hashed. Shared project objects are excluded from the proposed compiler search path.',
        'planner': file_record(Path(__file__))}
    (RUN/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps(manifest['summary'],indent=2))
    print('Changed:', changed)
    print('Missing:', [x['module'] for x in fresh if x['observed_shared_object'] is None])

if __name__ == '__main__': main()
