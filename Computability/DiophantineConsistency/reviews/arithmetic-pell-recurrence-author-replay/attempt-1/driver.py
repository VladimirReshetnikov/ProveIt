from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PLAN = DC / 'research/arithmetic-pell-recurrence-cache-plan.json'
PROPOSAL = DC / 'research/arithmetic-pell-recurrence-plan.md'
NAMES = ['DiophantineConsistency.ArithmeticPellRecurrence',
         'DiophantineConsistency.ArithmeticPellRecurrenceChecks']

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def record(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')

def check(x):
    actual = record(x['path'])
    require(actual['sha256'] == x['sha256'], 'hash ' + x['path'])
    if 'bytes' in x:
        require(actual['bytes'] == x['bytes'], 'size ' + x['path'])

def imports(path):
    # The selected sources were checked by the frozen read-only inventory.
    # New leaves use plain imports; no source interpreter is executed here.
    lines = Path(path).read_text().splitlines()
    return ['Init', *[m[1] for line in lines if
        (m := re.fullmatch(r'import\s+([A-Za-z_][A-Za-z_0-9.]*)', line))]]

check(dict(path=str(PLAN), sha256='dea799d5151a9a1024f975c2740d9aa23bf81a0965db5b60768b347242f95035'))
plan = json.loads(PLAN.read_text())
require(plan['counts'] == dict(custom=95, Foundation=95, artifacts=380,
        external=38, external_companions=114, fresh_prerequisites=0), 'exact scope')
for pin in plan['pins']:
    check(pin)
sources = [dict(module=name, **record(DC / 'Lean' / (name.replace('.', '/') + '.lean')))
           for name in NAMES]
require(imports(sources[0]['path']) == ['Init', *plan['direct_imports']], 'main imports')
require(imports(sources[1]['path']) == ['Init', NAMES[0]], 'checks imports')
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'initial reserve')
private = Path(tempfile.mkdtemp(prefix='arithmetic-pell-recurrence-author-'))
lib = private / 'lib'; logs = private / 'logs'
lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__, private / 'driver.py')
shutil.copyfile(PLAN, private / 'plan.json')
shutil.copyfile(PROPOSAL, private / 'proposal.md')
for s in sources:
    shutil.copyfile(s['path'], private / (s['module'].split('.')[-1] + '.input.lean'))
for item in plan['modules']:
    folder = lib / Path(item['module'].replace('.', '/')).parent
    folder.mkdir(parents=True, exist_ok=True)
    for obj in item['objects']:
        (folder / Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path = [str(lib), *plan['boundary_search']]
inputs = dict(plan=record(PLAN), proposal=record(PROPOSAL), sources=sources,
              compiler=plan['compiler'], LEAN_PATH=lean_path, pins=plan['pins'])
save(private / 'inputs.json', inputs)
state = dict(status='RUNNING', private=str(private), driver=record(__file__),
             inputs=record(private / 'inputs.json'), records=[])
save(private / 'state.json', state)
Path('/tmp/arithmetic-pell-recurrence-author-latest').write_text(str(private) + '\n')
with Path('/tmp/arithmetic-pell-recurrence-author-attempts').open('a') as f:
    f.write(str(private) + '\n')
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
print('PRIVATE ' + str(private), flush=True)
try:
    for source, expected in zip(sources, [0, 9]):
        require(shutil.disk_usage(private).free >= 512*1024**2, 'before command reserve')
        check(source)
        short = source['module'].split('.')[-1]
        output = lib / (source['module'].replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        require(not output.exists() and not output.is_symlink(), 'fresh output')
        log = logs / (short + '.log'); timing = logs / (short + '.time')
        snapshot = logs / (short + '.lean')
        shutil.copyfile(source['path'], snapshot)
        command = [plan['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
                   '-o', str(output), source['path']]
        print('START ' + short, flush=True)
        start = time.monotonic()
        with log.open('w') as f:
            code = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                                  cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
        entry = dict(module=source['module'], source=source, command=command,
                     snapshot=record(snapshot), exit_code=code, seconds=time.monotonic()-start,
                     log=record(log), timing=record(timing))
        state['records'].append(entry); save(private / 'state.json', state)
        print(log.read_text(), flush=True)
        require(code == 0, 'compile ' + short)
        require(not re.search(r'\b(?:warning|error|sorryAx)\b', log.read_text()), 'clean diagnostics')
        reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log.read_text())
        require(len(reports) == expected, 'report count')
        for name, axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'standard axioms ' + name)
        require(output.is_file() and not output.is_symlink(), 'regular output')
        entry.update(object=record(output), axiom_reports=reports)
        save(private / 'state.json', state)
        check(source)
    for pin in plan['pins']:
        check(pin)
    require(shutil.disk_usage(private).free >= 512*1024**2, 'final reserve')
    state.update(status='PASS', final_free_bytes=shutil.disk_usage(private).free)
    save(private / 'state.json', state)
    print('PASS ' + str(private), flush=True)
except BaseException as error:
    state.update(status='FAILED', failure=str(error)); save(private / 'state.json', state)
    raise
