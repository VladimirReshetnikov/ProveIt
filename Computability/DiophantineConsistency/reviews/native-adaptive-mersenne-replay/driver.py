from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
AUDIT = DC / 'research/adaptive-mersenne2011-cache-audit.json'
PROPOSAL = DC / 'research/adaptive-mersenne2011-proposal.md'
PROVIDER = DC / 'reviews/native-adaptive-power-recovery-root-replay/ROOT.json'
NAMES = ['DiophantineConsistency.NativeAdaptiveMersenne',
         'DiophantineConsistency.NativeAdaptiveMersenneChecks']

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def record(path):
    return {'path': str(path), 'sha256': sha(path), 'bytes': Path(path).stat().st_size}

def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def imports(path):
    text = path.read_text()
    out, i, depth = [], 0, 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; i += 2
            elif pair == '-/':
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; out.append(' '); i += 2
        elif pair == '--':
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            out.append(text[i]); i += 1
    require(depth == 0, 'unclosed comment')
    names, header = ['Init'], True
    for line in ''.join(out).splitlines():
        s = line.strip()
        if not s:
            continue
        m = re.fullmatch(r'import\s+([A-Za-z_][A-Za-z_0-9. ]*)', s)
        if m:
            require(header, 'late import ' + str(path))
            names.extend(m.group(1).split())
        else:
            header = False
    return list(dict.fromkeys(names))

require(sha(AUDIT) == '235165731675608064bfc92aa916b45cfecb6981016e9e3b6cf213a0673b9c3e', 'audit pin')
require(sha(PROPOSAL) == '6435d941d6a7beebc5fdb90d18db24e8e24d0e4be39f1c1ec56b952f1ab77b39', 'proposal pin')
require(sha(PROVIDER) == '9473432e98100b64f511acd679717a4ada8ccf4089d9ecfa206b40f66d51f495', 'provider pin')
scope = json.loads(AUDIT.read_text())
provider = scope
custom = {x['module']: x for x in scope['selected_custom']}
boundary = {x['module']: x for x in scope['external_boundary']}
require(len(custom) == 32 and len(boundary) == 22, '32/22 scope')
pins = {}

def pin(x):
    require(sha(x['path']) == x['sha256'], 'hash ' + x['path'])
    if x['path'] in pins:
        require(pins[x['path']]['sha256'] == x['sha256'], 'conflicting pin')
    pins[x['path']] = x

for p in (AUDIT, PROPOSAL, PROVIDER, Path(__file__)):
    pin(record(p))
pin(provider['compiler'])
for item in provider['parent_pins']:
    pin(item)
pin(provider['parent_inventory'])
for item in provider['api_sources']:
    pin(item)
for item in custom.values():
    pin(item['source']); pin(item['object'])
    require(imports(Path(item['source']['path'])) == item['actual_imports'], 'current imports ' + item['module'])
    require(set(item['actual_imports']) <= set(custom) | set(boundary), 'unresolved custom import')
for item in boundary.values():
    pin(item['source'])
    for obj in item['artifacts']:
        pin(obj)
sources = [dict(module=n, **record(DC / 'Lean' / (n.replace('.', '/') + '.lean'))) for n in NAMES]
require(imports(Path(sources[0]['path'])) == ['Init', 'DiophantineConsistency.NativeAdaptivePowerRecovery'], 'main imports')
require(imports(Path(sources[1]['path'])) == ['Init', NAMES[0]], 'checks imports')
for s in sources:
    pin(s)
require(shutil.disk_usage('/tmp').free >= 512*1024**2, '512MiB initial reserve')
private = Path(tempfile.mkdtemp(prefix='native-adaptive-mersenne-'))
lib = private / 'lib'; logs = private / 'logs'
lib.mkdir(); logs.mkdir()
for item in custom.values():
    target = lib / (item['module'].replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(Path(item['object']['path']).resolve())
lean_path = [str(lib), *provider['LEAN_PATH_template'][1:]]
inputs = dict(selected_custom=list(custom.values()), external_boundary=list(boundary.values()),
              sources=sources, compiler=provider['compiler'], pins=list(pins.values()), LEAN_PATH=lean_path,
              scope='32 authenticated reused custom modules;22 external names including Init;66 boundary object companions. Two new leaves only, reusing independently accepted root Power mains. No prerequisite or Foundation build.')
save(private / 'inputs.json', inputs)
state = dict(status='RUNNING', private=str(private), driver=record(__file__),
             inputs=record(private / 'inputs.json'), completed=[])
save(private / 'state.json', state)
Path('/tmp/native-adaptive-mersenne-latest').write_text(str(private) + '\n')
with Path('/tmp/native-adaptive-mersenne-attempts').open('a') as f:
    f.write(str(private)+'\n')
print('PRIVATE ' + str(private) + ' PINS ' + str(len(pins)), flush=True)
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
try:
    for s, expected in zip(sources, [0, 8]):
        require(shutil.disk_usage(private).free >= 512*1024**2, '512MiB before command')
        pin(s)
        short = s['module'].split('.')[-1]
        output = lib / (s['module'].replace('.', '/') + '.olean')
        require(not output.exists() and not output.is_symlink(), 'fresh output must be absent')
        snapshot = logs / (short + '.lean'); snapshot.write_bytes(Path(s['path']).read_bytes())
        log = logs / (short + '.log'); timing = logs / (short + '.time')
        command = [provider['compiler']['path'], '-M6000', '-j1', '-DElab.async=false', '-o', str(output), s['path']]
        start = time.monotonic()
        print('START ' + short, flush=True)
        with log.open('w') as f:
            code = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                                  cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
        entry = dict(module=s['module'], source=s, command=command, exit_code=code,
                     seconds=time.monotonic()-start, snapshot=record(snapshot), log=record(log), timing=record(timing))
        state['completed'].append(entry); save(private / 'state.json', state)
        print(log.read_text(), flush=True)
        require(code == 0, 'compile ' + short)
        reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log.read_text())
        require(len(reports) == expected, 'axiom report count')
        for name, axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'axioms ' + name)
        require(not output.is_symlink(), 'new output is not regular')
        entry.update(object=record(output), axiom_reports=reports)
        save(private / 'state.json', state)
        pin(s)
    for item in list(pins.values()):
        pin(item)
    require(shutil.disk_usage(private).free >= 512*1024**2, '512MiB final reserve')
    state.update(status='PASS', free_bytes=shutil.disk_usage(private).free)
    save(private / 'state.json', state)
    print('PASS ' + str(private), flush=True)
except BaseException as error:
    state.update(status='FAILED', failure=str(error)); save(private / 'state.json', state)
    raise
