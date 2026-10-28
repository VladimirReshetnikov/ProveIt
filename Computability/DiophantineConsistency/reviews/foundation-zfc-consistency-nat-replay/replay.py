"""Author replay of the fixed standard-Nat target; no prerequisite builds."""
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
NAMES = ['FoundationZFCConsistencyNat', 'FoundationZFCConsistencyNatChecks']


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


accepted = Path('/tmp/fixed-consistency73-root-xu0y__b6')
plan_path, state_path = accepted/'plan.json', accepted/'state.json'
p = json.loads(plan_path.read_text())
state = json.loads(state_path.read_text())
require(state['status'] == 'PASS' and state['plan_sha256'] == sha(plan_path),
        'Root scoped refresh is not accepted PASS')
require(len(state['completed']) == 73, 'Root fresh count')
check(p['compiler']); check(p['driver'])
for old in p['pins']:
    check(old)
fresh = {x['module']: x for x in state['completed']}
require(len(fresh) == 73 and all(x['exit_code'] == 0 for x in fresh.values()), 'Fresh failures')
for row in fresh.values():
    for key in ['source','snapshot','object','log']:
        check(row[key])
base = {}
for row in p['modules']:
    actual = imports(row['source']['path'])
    require(actual == row['actual_imports'], 'Source imports changed: ' + row['module'])
    objects = [fresh[row['module']]['object']] if row['action']=='fresh' else row['objects']
    if row['action']=='fresh':
        require(row['source'] == fresh[row['module']]['source'], 'Fresh source identity')
        require(not row['module'].startswith('Foundation.'), 'Unexpected Foundation fresh')
    else:
        require(not any(n in fresh for n in actual), 'Reused client imports a fresh dependency')
    base[row['module']] = dict(module=row['module'],source=row['source']['path'],
        source_sha256=row['source']['sha256'],objects=objects,imports=actual,
        origin='root73 fresh' if row['action']=='fresh' else 'root authenticated reuse')
g = p['additional_generic']
base[g['module']] = dict(module=g['module'],source=g['source']['path'],
    source_sha256=g['source']['sha256'],objects=[g['object']],
    imports=imports(g['source']['path']),origin='accepted generic Nat-semantics leaf')
ext_path = DC/'reviews/fixed-consistency-nat-cache-audit/external-boundaries.json'
ext = json.loads(ext_path.read_text())
external_rows = ext['modules']
external = {x['module'] for x in external_rows}
require(len(base)==410 and len(external)==51, 'Expected root410/51 closure')
require(sum(n.startswith('Foundation.') for n in base)==139, 'Foundation count')
ordered, seen = [], set()
def visit(n):
    if n in seen or n in external:
        return
    require(n in base, 'Uncached custom dependency: '+n)
    row=base[n]
    require(sha(row['source'])==row['source_sha256'], 'Source drift: '+n)
    for dependency in row['imports']:
        visit(dependency)
    seen.add(n); ordered.append(row)
for n in base:
    visit(n)
pins = p['pins'] + [pin(plan_path),pin(state_path),pin(ext_path),pin(__file__),p['driver']]
for old in fresh.values():
    pins.extend(old[key] for key in ['source','snapshot','object','log'])
for row in ordered:
    pins.append({'path':row['source'],'sha256':row['source_sha256']})
    pins.extend(row['objects'])
unique = {}
for record in pins:
    check(record)
    path = record['path']
    if path in unique:
        require(unique[path]['sha256'] == record['sha256'], 'Conflicting pin')
    unique[path] = {'path': path, 'sha256': record['sha256']}
pins = list(unique.values())
private = Path(tempfile.mkdtemp(prefix='fixed-zfc-nat-author-'))
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
inputs = {'status': 'AUTHENTICATED_BEFORE_EXECUTION', 'private': str(private),
          'modules': ordered, 'external': external_rows, 'pins': pins,
          'compiler': p['compiler'], 'lean_path': lean_path, 'driver': pin(__file__),
          'scope': '410 cached prerequisites from accepted73fresh+337reuse root overlay;139Foundation;51 external names. Only fixed Nat main/check freshly compiled.'}
shutil.copyfile(plan_path, run_dir/'root-plan.json')
shutil.copyfile(state_path, run_dir/'root-state.json')
shutil.copyfile(p['driver']['path'], run_dir/'root-driver.py')
inputs['root_plan']=pin(run_dir/'root-plan.json')
inputs['root_state']=pin(run_dir/'root-state.json')
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
