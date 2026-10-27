"""Author replay of two new C222 full-step leaves; never builds dependencies."""
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
NAMES = ['ArithmeticEnumStepPerm222', 'ArithmeticEnumStepPerm222Checks']


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


step_summary = DC/'reviews/arithmetic-command-stepperm222-replay.json'
fetch_summary = DC/'reviews/arithmetic-command-fetchperm222-replay.json'
s = json.loads(step_summary.read_text())
f = json.loads(fetch_summary.read_text())
require(s['status'] == 'PASS' and f['status'] == 'PASS', 'Parent status')
check(s['inputs']); check(s['final_result'])
p = json.loads(Path(s['inputs']['path']).read_text())
require(p['compiler']['sha256'] == f['inputs']['compiler_sha256'], 'Compiler mismatch')
base = {x['module']: x for x in p['modules']}
require(len(base) == 106, 'Expected step106')
pins = p['pins'] + f['inputs']['pins'] + [pin(step_summary), pin(fetch_summary),
        s['inputs'], s['final_result'], pin(__file__)]
for row in f['inputs']['modules']:
    require(row['module'] in base, 'Unexpected fetch prerequisite')
    require(base[row['module']]['source_sha256'] == row['source_sha256'], 'Parent source conflict')
    pins.append({'path': row['source'], 'sha256': row['source_sha256']})
    pins.extend(row['objects'])
for record in [s['records'][0], f['final_records'][0]]:
    require(record['exit_code'] == 0, 'Failed parent')
    base[record['module']] = {'module': record['module'],
        'source': record['source']['path'], 'source_sha256': record['source']['sha256'],
        'objects': [record['object']], 'imports': imports(record['source']['path']),
        'provenance': 'accepted fresh parent main'}
    pins.extend(record[k] for k in ['source','snapshot','log','object'])
external = {x['module'] for x in p['external']}
require(external == {x['module'] for x in f['inputs']['external']}, 'External union changed')
ordered, seen = [], set()
def visit(n):
    if n in seen or n in external:
        return
    require(n in base, 'Uncached custom dependency: '+n)
    row = base[n]
    require(sha(row['source']) == row['source_sha256'], 'Source drift: '+n)
    actual = imports(row['source'])
    require(actual == row['imports'], 'Import drift: '+n)
    require(not any(x == 'DiophantineConsistency.'+new for x in actual for new in NAMES),
            'Reused client imports new leaf')
    for dependency in actual:
        visit(dependency)
    seen.add(n); ordered.append(row)
visit('DiophantineConsistency.ArithmeticCommandFetchPerm222')
visit('DiophantineConsistency.ArithmeticCommandStepPerm222')
require(len(ordered) == len(base) == 108, 'Expected108 current modules')
require(sum(x['module'].startswith('Foundation.') for x in ordered) == 86, 'Foundation count')
require(len(external) == 37, 'Boundary count')
for row in ordered:
    pins.append({'path': row['source'], 'sha256': row['source_sha256']})
    pins.extend(row['objects'])
unique = {}
for record in pins:
    check(record)
    path = str(Path(record['path']).resolve())
    require(path not in unique or unique[path]['sha256'] == record['sha256'], 'Conflicting pin')
    unique[path] = {'path': path, 'sha256': record['sha256']}
pins = list(unique.values())
private = Path(tempfile.mkdtemp(prefix='enum-stepperm222-author-'))
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
for label, parent in [('step', step_summary), ('fetch', fetch_summary)]:
    shutil.copyfile(parent, run_dir/(label+'-parent.json'))
inputs = {'status': 'AUTHENTICATED_BEFORE_EXECUTION', 'private': str(private),
          'modules': ordered, 'external': p['external'], 'pins': pins,
          'compiler': p['compiler'], 'lean_path': lean_path, 'driver': pin(__file__),
          'scope': '108 cached current-source pairs;86Foundation;37 external names; only new main/check freshly compiled.'}
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
require(len(records[1]['axiom_reports']) == 11, 'Expected eleven checks reports')
result = {'status': 'PASS', 'inputs': pin(run_dir/'inputs.json'), 'records': records,
          'private': str(private), 'all_pre_post_pins_match': True, 'driver': pin(__file__)}
save(run_dir/'RESULT.json', result)
save(HERE/'LATEST.json', {'result': pin(run_dir/'RESULT.json')})
print(json.dumps({'status': 'PASS', 'private': str(private), 'result': str(run_dir/'RESULT.json'),
                  'seconds': [x['seconds'] for x in records]}), flush=True)
