"""Independent replay of the frozen internal EnumPerm command-evaluation pair.
No dependency compilation; all outputs are new private regular files.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import tempfile
import time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REVIEWS = ROOT / 'Computability/DiophantineConsistency/reviews'
HERE = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}


def check(p):
    require(sha(p['path']) == p['sha256'], 'Changed pin: ' + p['path'])


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def imports(source):
    # Independent header parser: remove nested comments, preserving newlines.
    text = Path(source).read_text()
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; i += 2
            elif pair == '-/':
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i+1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif pair == '/-':
            depth = 1; out.append(' '); i += 2
        elif pair == '--':
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            quoted = text[i] == '"'
            out.append(text[i]); i += 1
    require(depth == 0, 'Unclosed comment in ' + str(source))
    result, prelude = [], False
    for line in ''.join(out).splitlines():
        line = line.strip()
        if not line:
            continue
        if line in ['module', 'prelude']:
            prelude |= line == 'prelude'; continue
        match = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)', line)
        if not match:
            break
        names = match.group(1).split()
        require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names), 'Import syntax')
        result.extend(names)
    if not prelude:
        result.insert(0, 'Init')
    return list(dict.fromkeys(result))


summary_path = REVIEWS/'arithmetic-command-evaluationperm222-replay.json'
require(sha(summary_path) == '6b3bd0bf63a2d80ecf4818965fb62a34fd7b7ac191e69635ac25bf803cd0c113',
        'Frozen author summary changed')
author = json.loads(summary_path.read_text())
require(author['status'] == 'PASS', 'Author not PASS')
for key in ['inputs', 'driver', 'attempt', 'bundle_manifest']:
    check(author[key])
source_inputs = Path(author['inputs']['path'])
data = json.loads(source_inputs.read_text())
modules = {r['module']: r for r in data['modules']}
external = {r['module']: r for r in data['external']}
fresh = {r['module'] for r in author['records']}
require(len(modules) == 118, '118 cached modules expected')
require(sum(n.startswith('Foundation.') for n in modules) == 95, 'Foundation count')
require(sum(len(r['objects']) for r in modules.values()) == 403, 'Cached artifact count')
require(len(external) == 38, 'External count')
ordered, visiting, done, used_external = [], set(), set(), set()
import_normalizations = []


def visit(name):
    if name in external:
        used_external.add(name)
        return
    require(name in modules, 'Missing custom import: '+name)
    require(name not in visiting, 'Import cycle: '+name)
    if name in done:
        return
    row = modules[name]
    require(sha(row['source']) == row['source_sha256'], 'Source drift: '+name)
    actual = imports(row['source'])
    recorded = list(dict.fromkeys(row['imports']))
    if actual != recorded:
        require(name == 'DiophantineConsistency.ArithmeticCommandRunPerm222' and
                actual == ['Init', *recorded], 'Import metadata mismatch: '+name)
        import_normalizations.append({'module': name, 'recorded': recorded, 'actual': actual,
                                      'reason': 'Explicit source imports omitted implicit Init'})
    row = {**row, 'imports': actual}
    require(not any(n in fresh for n in actual), 'Cached client imports fresh leaf')
    visiting.add(name)
    for dep in actual:
        visit(dep)
    visiting.remove(name)
    done.add(name)
    ordered.append(row)


for row in author['records']:
    for dep in imports(row['source']['path']):
        if dep not in fresh:
            visit(dep)
require(done == set(modules) and used_external == set(external), 'Extraneous/incomplete closure')
pins = [pin(summary_path), author['inputs'], author['driver'], author['attempt'],
        author['bundle_manifest'], pin(__file__), data['compiler'], *data['pins']]
for path, expected in [('lean-toolchain', '2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e'),
        ('lake-manifest.json', '95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665')]:
    record = pin(ROOT/path)
    require(record['sha256'] == expected, 'Toolchain/package mismatch')
    pins.append(record)
for row in ordered:
    pins.append({'path': row['source'], 'sha256': row['source_sha256']})
    pins.extend(row['objects'])
for row in author['records']:
    for key in ['source', 'snapshot', 'log', 'timing', 'object']:
        pins.append(row[key])
manifest = json.loads(Path(author['bundle_manifest']['path']).read_text())
bundle = Path(author['bundle_manifest']['path']).parent
bundle_rows = manifest['files'] if isinstance(manifest, dict) else manifest
for item in bundle_rows:
    source = bundle/item['path']
    require(sha(source) == item['sha256'], 'Changed author bundle member')
    pins.append(pin(source))
unique = {}
for record in pins:
    check(record)
    path = str(Path(record['path']).resolve())
    require(path not in unique or unique[path]['sha256'] == record['sha256'], 'Pin conflict')
    unique[path] = {'path': path, 'sha256': record['sha256']}
pins = list(unique.values())
require(shutil.disk_usage(ROOT).free >= 512*1024*1024, '512MiB reserve')
private = Path(tempfile.mkdtemp(prefix='command-evaluationperm222-independent-'))
lib = private/'lib'
lib.mkdir()
for row in ordered:
    for obj in row['objects']:
        target = lib/Path(*row['module'].split('.')[:-1])/Path(obj['path']).name
        target.parent.mkdir(parents=True, exist_ok=True)
        require(not target.exists() and not target.is_symlink(), 'Existing cache output')
        target.symlink_to(obj['path'])
attempt = HERE/('attempt-'+str(time.time_ns()))
attempt.mkdir()
shutil.copyfile(summary_path, attempt/'author-summary.json')
shutil.copyfile(source_inputs, attempt/'author-inputs.json')
lean_path = ':'.join([str(lib), *data['lean_path'].split(':')[1:]])
inputs = {'status': 'AUTHENTICATED_BEFORE_EXECUTION', 'private': str(private),
          'modules': ordered, 'external': data['external'], 'pins': pins,
          'import_normalizations': import_normalizations,
          'author': pin(summary_path), 'compiler': data['compiler'], 'lean_path': lean_path,
          'driver': pin(__file__), 'scope': '118 cached/95Foundation/403 artifacts/38 boundaries; only new pair fresh.'}
save(attempt/'inputs.json', inputs)
env = os.environ.copy()
env['LEAN_PATH'] = lean_path
env['LEAN_NUM_THREADS'] = '1'
env.pop('LEAN_SRC_PATH', None)
records = []
for row in author['records']:
    require(shutil.disk_usage(ROOT).free >= 512*1024*1024, '512MiB reserve')
    for record in pins:
        check(record)
    name = row['module']
    source = Path(row['source']['path'])
    snapshot = attempt/(name+'.lean')
    shutil.copyfile(source, snapshot)
    output = lib/Path(*name.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    require(not output.exists() and not output.is_symlink(), 'Fresh output exists')
    log = attempt/(name+'.log')
    command = [data['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
               '-o', str(output), str(source)]
    start = time.monotonic()
    with log.open('w') as stream:
        code = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                              stderr=subprocess.STDOUT).returncode
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                         log.read_text())
    result = {'module': name, 'source': pin(source), 'snapshot': pin(snapshot),
              'command': command, 'exit_code': code, 'seconds': time.monotonic()-start,
              'log': pin(log), 'object': pin(output) if code == 0 else None,
              'author_object_equal': code == 0 and sha(output) == row['object']['sha256'],
              'axiom_reports': reports, 'child_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
    records.append(result)
    save(attempt/(name+'.json'), result)
    for record in pins:
        check(record)
    require(sha(source) == sha(snapshot), 'Source drift while compiling')
    if code:
        save(attempt/'RESULT.json', {'status': 'FAILED', 'inputs': pin(attempt/'inputs.json'),
                                    'records': records})
        raise SystemExit(code)
    for title, axioms in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*', axioms)) <=
                {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom: '+title)
require(not Path(records[0]['log']['path']).read_text(), 'Main diagnostics')
require(len(records[1]['axiom_reports']) == 6, 'Expected6 audits')
result = {'status': 'PASS', 'inputs': pin(attempt/'inputs.json'), 'driver': pin(__file__),
          'records': records, 'all_pre_post_pins_match': True, 'private': str(private)}
save(attempt/'RESULT.json', result)
save(HERE/'LATEST.json', {'result': pin(attempt/'RESULT.json')})
print(json.dumps({'status': 'PASS', 'private': str(private), 'result': str(attempt/'RESULT.json'),
                  'seconds': [r['seconds'] for r in records],
                  'matches_author': [r['author_object_equal'] for r in records], 'pins': len(pins)}))

