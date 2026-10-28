"""Author replay of finite bounded double-negation leaves; never builds dependencies."""
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
DC = ROOT / 'Computability/DiophantineConsistency'
HERE = Path(__file__).resolve().parent
NAMES = ['HABoundedDoubleNegation', 'HABoundedDoubleNegationChecks']


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


audit_path = DC/'research/ha-negative-sigma-one-calibration-pins.json'
require(sha(audit_path) == '92033bccee10d1018c9d4cc52543a289fe99a09d4fa64813fd47601f707ed2c3', 'Audit pins drift')
audit = json.loads(audit_path.read_text())
selected = audit['first_leaf']
check(selected['parent_summary']); check(selected['parent_inputs'])
summary_path = Path(selected['parent_summary']['path'])
summary = json.loads(summary_path.read_text())
require(summary['status'] == 'PASS', 'Parent not PASS')
parent = json.loads(Path(selected['parent_inputs']['path']).read_text())
base = {x['module']: x for x in selected['modules']}
root_peer_path = DC/'reviews/ha-bounded-quantifiers-root-replay/ROOT.json'
require(sha(root_peer_path) == '8a321ccb5e0f1860701fd8e1e5319027de7ccc8e15458aac09a286ead4b9808c', 'Root bounded provider drift')
root_peer = json.loads(root_peer_path.read_text())
require(root_peer['status'] == 'PASS', 'Root provider not PASS')
new_parent = root_peer['records'][0]
require(new_parent['module'] == 'DiophantineConsistency.HABoundedQuantifiers', 'Wrong provider')
for key in ['source', 'object', 'log']:
    check(new_parent[key])
require(base[new_parent['module']]['objects'][0] == new_parent['object'], 'Root primary not selected')
external_all = {x['module']: x for x in parent['external']}
ordered, seen, external = [], set(), set()
def visit(n):
    if n in seen:
        return
    if n in external_all:
        external.add(n); return
    require(n in base, 'Missing current provider: '+n)
    row = base[n]
    require(sha(row['source']) == row['source_sha256'], 'Source drift: '+n)
    actual = imports(row['source'])
    require(actual == row['imports'], 'Import drift: '+n)
    require(not any(x == 'DiophantineConsistency.'+new for x in actual for new in NAMES),
            'Reused client imports new leaf')
    for dep in actual:
        visit(dep)
    seen.add(n); ordered.append(row)
visit('DiophantineConsistency.HABoundedQuantifiers')
require(len(ordered) == 101, 'Expected101 prerequisites')
require(sum(x['module'].startswith('Foundation.') for x in ordered) == 76, 'Foundation count')
require(len(external) == 34, 'Boundary count')
pins = [pin(audit_path), pin(root_peer_path), pin(summary_path), summary['inputs'], summary['result'], summary['bundle_files'],
        parent['compiler'], pin(__file__), *parent['pins']]
for record in summary['records']:
    for key in ['source', 'snapshot', 'log', 'object']:
        pins.append(record[key])
for record in root_peer['records']:
    for key in ['source', 'log', 'object']:
        pins.append(record[key])
parent_manifest = json.loads(Path(summary['bundle_files']['path']).read_text())
for record in parent_manifest['files']:
    path = Path(summary['bundle_files']['path']).parent / record['path']
    require(sha(path) == record['sha256'], 'Original parent bundle drift')
    pins.append(pin(path))
for filename, expected in [('lean-toolchain','2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e'),
        ('lake-manifest.json','95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665')]:
    record = pin(ROOT/filename)
    require(record['sha256'] == expected, 'Package/compiler version changed')
    pins.append(record)
for row in ordered:
    pins.append({'path': row['source'], 'sha256': row['source_sha256']})
    pins.extend(row['objects'])
external_rows = [external_all[n] for n in sorted(external)]
for row in external_rows:
    if row.get('source'):
        pins.append(row['source'])
    pins.extend(row['objects'])
unique = {}
for record in pins:
    check(record)
    path = str(Path(record['path']).resolve())
    require(path not in unique or unique[path]['sha256'] == record['sha256'], 'Conflicting pin')
    unique[path] = {'path': path, 'sha256': record['sha256']}
pins = list(unique.values())
p = dict(parent, external=external_rows)
require(shutil.disk_usage(ROOT).free >= 512*1024*1024, '512MiB disk reserve before overlay')
private = Path(tempfile.mkdtemp(prefix='ha-bounded-double-negation-author-'))
lib = private / 'lib'
lib.mkdir()
for row in ordered:
    for obj in row['objects']:
        check(obj)
        dest = lib / Path(*row['module'].split('.')[:-1]) / Path(obj['path']).name
        dest.parent.mkdir(parents=True, exist_ok=True)
        require(not dest.exists() and not dest.is_symlink(), 'Existing cache output')
        dest.symlink_to(obj['path'])
run_dir = HERE / ('attempt-' + str(time.time_ns()))
run_dir.mkdir()
lean_path = ':'.join([str(lib), *p['lean_path'].split(':')[1:]])
shutil.copyfile(summary_path, run_dir/'parent-summary.json')
shutil.copyfile(summary['inputs']['path'], run_dir/'parent-inputs.json')
inputs = {'status': 'AUTHENTICATED_BEFORE_EXECUTION', 'private': str(private),
          'modules': ordered, 'external': p['external'], 'pins': pins,
          'compiler': p['compiler'], 'lean_path': lean_path, 'driver': pin(__file__),
          'scope': '101 cached current-source pairs;76Foundation;34 external names; only new main/check freshly compiled.'}
save(run_dir / 'inputs.json', inputs)
env = os.environ.copy()
env['LEAN_PATH'] = lean_path
env['LEAN_NUM_THREADS'] = '1'
env.pop('LEAN_SRC_PATH', None)
records = []
for name in NAMES:
    require(shutil.disk_usage(ROOT).free >= 512*1024*1024, '512MiB disk reserve')
    for record in pins:
        check(record)
    source = DC / 'Lean/DiophantineConsistency' / (name + '.lean')
    require(all(n in seen or n in external or n == 'DiophantineConsistency.' + NAMES[0]
                for n in imports(source)), 'New import outside selected closure')
    snapshot = run_dir / (name + '.lean')
    shutil.copyfile(source, snapshot)
    output = lib / 'DiophantineConsistency' / (name + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    require(not output.exists() and not output.is_symlink(), 'Fresh output would overwrite')
    log = run_dir / (name + '.log')
    command = [p['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
               '-o', str(output), str(source)]
    start = time.monotonic()
    with log.open('w') as stream:
        code = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                              stderr=subprocess.STDOUT).returncode
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                         log.read_text())
    rec = {'module': 'DiophantineConsistency.' + name, 'source': pin(source),
           'snapshot': pin(snapshot), 'command': command, 'exit_code': code,
           'seconds': time.monotonic()-start, 'log': pin(log),
           'object': pin(output) if code == 0 else None, 'axiom_reports': reports,
           'child_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
    records.append(rec)
    save(run_dir / (name + '.json'), rec)
    require(sha(source) == sha(snapshot), 'Source changed during execution')
    for record in pins:
        check(record)
    if code:
        failure = {'status': 'FAILED', 'inputs': pin(run_dir/'inputs.json'),
                   'records': records, 'private': str(private)}
        save(run_dir/'RESULT.json', failure)
        print(json.dumps(failure), flush=True)
        raise SystemExit(code)
    for title, axioms in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*', axioms)) <=
                {'propext', 'Quot.sound', 'Classical.choice'}, 'Unexpected axioms: ' + title)
require(not Path(records[0]['log']['path']).read_text(), 'Unexpected main diagnostics')
require(len(records[1]['axiom_reports']) == 8, 'Expected eight checks reports')
result = {'status': 'PASS', 'inputs': pin(run_dir/'inputs.json'), 'records': records,
          'private': str(private), 'all_pre_post_pins_match': True, 'driver': pin(__file__)}
save(run_dir/'RESULT.json', result)
save(HERE/'LATEST.json', {'result': pin(run_dir/'RESULT.json')})
print(json.dumps({'status': 'PASS', 'private': str(private), 'result': str(run_dir/'RESULT.json'),
                  'seconds': [x['seconds'] for x in records]}), flush=True)
