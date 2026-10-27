"""Two fresh HA leaves over the accepted fixed-Nat/current-transfer union."""
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
REV = DC / 'reviews'
HERE = Path(__file__).resolve().parent
NAMES = ['FoundationHAZFCValidator', 'FoundationHAZFCValidatorChecks']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}


def check(record):
    require(sha(record['path']) == record['sha256'], 'Changed pin: ' + record['path'])


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def imports(source):
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
    require(depth == 0, 'Unclosed comment')
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
        require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names),
                'Unsupported import syntax')
        result.extend(names)
    if not prelude:
        result.insert(0, 'Init')
    return list(dict.fromkeys(result))


parents = {
    'fixed_summary': REV/'foundation-zfc-consistency-nat-replay.json',
    'fixed_inputs': REV/'foundation-zfc-consistency-nat-replay/attempt-1793060769992598293/inputs.json',
    'transfer': REV/'foundation-ha-current-transfer-dependency-replay.json',
}
fixed = json.loads(parents['fixed_summary'].read_text())
a = json.loads(parents['fixed_inputs'].read_text())
b = json.loads(parents['transfer'].read_text())
require(fixed['status'] == 'PASS' and b['status'] == 'PASS', 'Unaccepted parent status')
require(a['compiler']['sha256'] == b['compiler']['sha256'], 'Compiler mismatch')
require(fixed['inputs'] == pin(parents['fixed_inputs']), 'Fixed input binding')
check(fixed['final_result'])
require(len(a['modules']) == 410 and len(b['modules']) == 133, 'Parent cache counts')
pins = list(a['pins']) + [pin(p) for p in parents.values()] + [pin(__file__)]
pins += [fixed['final_result'], a['compiler']]
for filename, identity in b['package_identity'].items():
    current = pin(ROOT/filename)
    require(current['sha256'] == identity['current_sha256'] == identity['cache_sha256'],
            'Package identity mismatch: ' + filename)
    pins.append(current)


def normalize(row, origin):
    objects = row.get('objects')
    if objects is None:
        objects = [{'path': row['object'], 'sha256': row['object_sha256']}]
    source = Path(row['source']).resolve()
    return {'module': row['module'], 'source': str(source),
            'source_sha256': row['source_sha256'], 'objects': objects,
            'imports': imports(source), 'origin': origin}


base = {x['module']: normalize(x, x['origin']) for x in a['modules']}
alternatives = []
for original in b['modules'] + [x for x in b['fresh_modules']
                              if not x['module'].endswith('Checks')]:
    row = normalize(original, 'accepted current-transfer packet')
    name = row['module']
    require(name not in base or base[name]['source_sha256'] == row['source_sha256'],
            'Conflicting source: ' + name)
    if name not in base:
        base[name] = row
    elif base[name]['objects'] != row['objects']:
        alternatives.append({'module': name, 'selected': base[name]['objects'],
                             'other_accepted': row['objects']})
    pins.append({'path': row['source'], 'sha256': row['source_sha256']})
    pins.extend(row['objects'])
for record in fixed['records']:
    if record['module'].endswith('Checks'):
        continue
    require(record['exit_code'] == 0, 'Failed fixed Nat main')
    base[record['module']] = {'module': record['module'],
        'source': record['source']['path'], 'source_sha256': record['source']['sha256'],
        'objects': [record['object']], 'imports': imports(record['source']['path']),
        'origin': 'accepted fixed Nat main'}
    pins.extend(record[k] for k in ['source', 'snapshot', 'log', 'object'])

external = {x['module']: x for x in a['external']}
for old in b['external']:
    check(old)
    if old['module'] in external:
        require(any(o['sha256'] == old['sha256'] for o in external[old['module']]['objects']),
                'Conflicting external primary: ' + old['module'])
        continue
    primary = Path(old['path'])
    package, relative = str(primary).split('/.lake/build/lib/lean/')
    source = Path(package)/(relative[:-len('.olean')] + '.lean')
    objects = [pin(primary)]
    missing = []
    for suffix in ['.olean.server', '.olean.private', '.ir']:
        companion = primary.with_suffix(suffix)
        if companion.exists():
            objects.append(pin(companion))
        else:
            missing.append(suffix)
    external[old['module']] = {'module': old['module'], 'source': pin(source),
        'objects': objects, 'missing_optional_companions': missing,
        'scope': 'Accepted package boundary; primary previously pinned, companions pinned here'}
for row in external.values():
    if row.get('source'):
        pins.append(row['source'])
    pins.extend(row['objects'])

require(len(base) == 448 and len(external) == 57, 'Expected448/57 union')
require(sum(n.startswith('Foundation.') for n in base) == 139, 'Foundation count')
ordered, seen = [], set()
fresh_names = {'DiophantineConsistency.' + n for n in NAMES}


def visit(name):
    if name in seen or name in external:
        return
    require(name in base, 'Missing custom provider: ' + name)
    row = base[name]
    require(not any(n in fresh_names for n in row['imports']),
            'Reused client imports a new fresh leaf')
    for dependency in row['imports']:
        visit(dependency)
    seen.add(name); ordered.append(row)


for name in ['DiophantineConsistency.FoundationZFCConsistencyNat',
             'DiophantineConsistency.FoundationHACurrentTransfer']:
    visit(name)
require(len(seen) == len(base), 'Unexpected unused cache entries')
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
private = Path(tempfile.mkdtemp(prefix='foundation-ha-zfc-validator-'))
lib = private/'lib'
lib.mkdir()
for row in ordered:
    for obj in row['objects']:
        dest = lib/Path(*row['module'].split('.')[:-1])/Path(obj['path']).name
        dest.parent.mkdir(parents=True, exist_ok=True)
        require(not dest.exists() and not dest.is_symlink(), 'Existing cache destination')
        dest.symlink_to(obj['path'])
run = HERE/('attempt-' + str(time.time_ns()))
run.mkdir()
parent_snapshots = {}
for label, path in parents.items():
    copy = run/(label + '.json')
    shutil.copyfile(path, copy)
    parent_snapshots[label] = pin(copy)
lean_path = ':'.join([str(lib), *a['lean_path'].split(':')[1:]])
inputs = {'scope': '448 cached current-source modules,139Foundation,57 explicit external boundaries; only two fresh leaves',
    'private': str(private), 'modules': ordered, 'external': list(external.values()),
    'pins': pins, 'compiler': a['compiler'], 'lean_path': lean_path,
    'driver': pin(__file__), 'parents': parent_snapshots, 'alternatives': alternatives}
save(run/'inputs.json', inputs)
env = os.environ.copy()
env['LEAN_PATH'] = lean_path
env['LEAN_NUM_THREADS'] = '1'
env.pop('LEAN_SRC_PATH', None)
records = []
for name in NAMES:
    require(shutil.disk_usage(ROOT).free >= 512*1024*1024, '512MiB disk reserve')
    for record in pins:
        check(record)
    source = DC/'Lean/DiophantineConsistency'/(name + '.lean')
    require(all(n in seen or n in external or n == 'DiophantineConsistency.' + NAMES[0]
                for n in imports(source)), 'New import outside selected closure')
    snapshot = run/(name + '.lean')
    shutil.copyfile(source, snapshot)
    output = lib/'DiophantineConsistency'/(name + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    require(not output.exists() and not output.is_symlink(), 'Fresh output would overwrite')
    log = run/(name + '.log')
    command = [a['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
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
    save(run/(name + '.json'), rec)
    require(sha(source) == sha(snapshot), 'Source changed during build')
    for record in pins:
        check(record)
    if code:
        save(run/'RESULT.json', {'status': 'FAILED', 'inputs': pin(run/'inputs.json'),
             'records': records, 'private': str(private)})
        print(str(run/'RESULT.json'), flush=True)
        raise SystemExit(code)
    for title, axioms in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*', axioms)) <=
                {'propext', 'Quot.sound', 'Classical.choice'}, 'Unexpected axioms: ' + title)
require(not Path(records[0]['log']['path']).read_text(), 'Unexpected main diagnostics')
require(len(records[1]['axiom_reports']) == 8, 'Expected8 reports')
result = {'status': 'PASS', 'inputs': pin(run/'inputs.json'), 'records': records,
          'private': str(private), 'all_pre_post_pins_match': True, 'driver': pin(__file__)}
save(run/'RESULT.json', result)
save(HERE/'LATEST.json', {'result': pin(run/'RESULT.json')})
print(json.dumps({'status': 'PASS', 'private': str(private), 'result': str(run/'RESULT.json'),
                  'seconds': [x['seconds'] for x in records]}), flush=True)
