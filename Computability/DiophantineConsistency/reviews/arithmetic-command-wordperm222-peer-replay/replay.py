"""Independent two-leaf replay; no dependency builds or shared output writes."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE = Path(__file__).resolve().parent
AUTHOR = Path('/tmp/wordperm222-root-author-595a4uou')
NAMES = ['ArithmeticCommandWordPerm222', 'ArithmeticCommandWordPerm222Checks']
EXPECTED = ['e871fd138de904e667803864882b80981a4cd3dcdc2416bfe7b9a76211cc3a7c',
            'cf96f36c2de2c88d650695e77d37d7b93ade1af915526be7f3ee9225d699ee89']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def check(record):
    require(sha(record['path']) == record['sha256'], 'Pin changed: ' + record['path'])


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


d = json.loads((AUTHOR / 'inputs.json').read_text())
final_run = json.loads((AUTHOR / 'run-1793059115674710626.json').read_text())
failed_run = json.loads((AUTHOR / 'run-1793059040016842800.json').read_text())
require(final_run['status'] == 'PASS' and failed_run['status'] == 'FAILED', 'Author run distinction')
require(final_run['inputs_sha256'] == sha(AUTHOR / 'inputs.json'), 'Author inputs changed')
require(len(d['modules']) == 101, 'Wrong custom closure')
require(sum(m['module'].startswith('Foundation.') for m in d['modules']) == 86, 'Foundation count')
require(len(d['external']) == 37, 'External boundary count')
require(d['compiler_sha256'] == sha(d['compiler']), 'Compiler changed')
require(sha('/tmp/wordperm222-root-build.py') == d['driver_sha256'], 'Author driver changed')
modules = {r['module']: r for r in d['modules']}
external = {r['module'] for r in d['external']}
seen = set()
for module, row in modules.items():
    require(sha(row['source']) == row['source_sha256'], 'Source mismatch: ' + module)
    actual = imports(row['source'])
    require(actual == row['imports'], 'Import metadata mismatch: ' + module)
    require(all(n in seen or n in external for n in actual), 'Closure/order gap: ' + module)
    seen.add(module)
for record in d['pins']:
    check(record)

private = Path(tempfile.mkdtemp(prefix='wordperm222-independent-'))
lib = private / 'lib'
lib.mkdir()
for module, row in modules.items():
    for obj in row['objects']:
        check(obj)
        target = lib / Path(*module.split('.')[:-1]) / Path(obj['path']).name
        target.parent.mkdir(parents=True, exist_ok=True)
        require(not target.exists() and not target.is_symlink(), 'Existing cache destination')
        target.symlink_to(obj['path'])
extra_pins = [pin(AUTHOR / 'inputs.json'), pin('/tmp/wordperm222-root-build.py'), pin(__file__)]
for p in sorted(AUTHOR.glob('*.json')):
    extra_pins.append(pin(p))
for run in [failed_run, final_run]:
    for record in run['records']:
        for key in ['snapshot', 'log']:
            check(record[key]); extra_pins.append(record[key])
        # Preserve author failure independently; it has no successful output object.
        if record['object']:
            check(record['object']); extra_pins.append(record['object'])
sources = []
for name, expected in zip(NAMES, EXPECTED):
    src = ROOT / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency' / (name + '.lean')
    require(sha(src) == expected, 'Frozen source changed: ' + name)
    sources.append(src); extra_pins.append(pin(src))
    shutil.copyfile(src, HERE / (name + '.lean'))
for file in [AUTHOR / 'inputs.json', Path('/tmp/wordperm222-root-build.py')]:
    shutil.copyfile(file, HERE / ('author-' + file.name))
for run_name in ['run-1793059040016842800.json', 'run-1793059115674710626.json']:
    shutil.copyfile(AUTHOR / run_name, HERE / ('author-' + run_name))
for record in failed_run['records']:
    for key in ['snapshot', 'log']:
        f = Path(record[key]['path'])
        shutil.copyfile(f, HERE / ('author-failed-' + f.name))
lean_path = ':'.join([str(lib), *d['lean_path'].split(':')[1:]])
inputs = {'status': 'AUTHENTICATED_BEFORE_EXECUTION', 'private': str(private),
          'author_inputs': pin(AUTHOR / 'inputs.json'), 'modules': d['modules'],
          'external': d['external'], 'pins': d['pins'] + extra_pins,
          'compiler': pin(d['compiler']), 'lean_path': lean_path,
          'driver': pin(__file__), 'sources': [pin(p) for p in sources],
          'scope': '101 current-source cached pairs,86Foundation,37 direct external boundaries. Only two new leaves freshly compiled.'}
save(HERE / 'inputs.json', inputs)
env = os.environ.copy()
env['LEAN_PATH'] = lean_path
env.pop('LEAN_SRC_PATH', None)
env['LEAN_NUM_THREADS'] = '1'
records = []
for name, src, author in zip(NAMES, sources, final_run['records']):
    require(shutil.disk_usage(private).free >= 512*1024*1024, '512MiB disk reserve')
    for record in inputs['pins']:
        check(record)
    output = lib / 'DiophantineConsistency' / (name + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    require(not output.exists() and not output.is_symlink(), 'Fresh output would overwrite')
    log = HERE / (name + '.log')
    command = [d['compiler'], '-M6000', '-j1', '-DElab.async=false', '-o', str(output), str(src)]
    start = time.monotonic()
    with log.open('w') as stream:
        code = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log.read_text())
    record = {'module': 'DiophantineConsistency.' + name, 'source': pin(src),
              'command': command, 'exit_code': code, 'seconds': time.monotonic()-start,
              'log': pin(log), 'object': pin(output) if code == 0 else None,
              'axiom_reports': reports,
              'author_object_equal': code == 0 and sha(output) == author['object']['sha256']}
    records.append(record)
    save(HERE / (name + '.json'), record)
    require(code == 0, 'Fresh compilation failed: ' + name)
    for title, axioms in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*', axioms)) <=
                {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axioms: ' + title)
    for old in inputs['pins']:
        check(old)
require(len(records[0]['axiom_reports']) == 0 and len(records[1]['axiom_reports']) == 9,
        'Expected exactly nine checks reports')
require(Path(records[0]['log']['path']).read_text() == '', 'Unexpected main diagnostics')
result = {'status': 'PASS', 'inputs': pin(HERE / 'inputs.json'), 'driver': pin(__file__),
          'records': records, 'all_pre_post_pins_match': True,
          'scope': inputs['scope'], 'private': str(private),
          'author_failure_separate': pin(HERE / 'author-run-1793059040016842800.json')}
save(HERE / 'RESULT.json', result)
print(json.dumps({'status': 'PASS', 'private': str(private), 'reports': 9,
                  'byte_identical': [r['author_object_equal'] for r in records],
                  'seconds': [r['seconds'] for r in records]}))
