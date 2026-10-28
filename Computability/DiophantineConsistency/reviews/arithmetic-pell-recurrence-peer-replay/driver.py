from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PACKET = DC / 'reviews/arithmetic-pell-recurrence-replay.json'
observations = {}

def record(path):
    path = Path(path); data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))

def require(ok, message):
    if not ok: raise RuntimeError(message)

def check(pin):
    actual = record(pin['path'])
    require(actual['sha256'] == pin['sha256'], 'hash ' + pin['path'])
    if 'bytes' in pin: require(actual['bytes'] == pin['bytes'], 'size ' + pin['path'])
    observations[actual['path']] = actual
    return actual

def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')

def imports(path):
    s = Path(path).read_text(); out = []; i = depth = 0
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            while i < len(s) and s[i] != '\n': i += 1
        else: out.append(s[i]); i += 1
    require(depth == 0, 'comment balance')
    return list(dict.fromkeys(['Init'] + [n for line in re.findall(
        r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', ''.join(out), re.M)
        for n in line.split()]))

check(dict(path=str(PACKET), sha256='022e44d19bec3bd4fe3de9e130d601ea31179bb73efcee51deb6233fe71e183d'))
packet = json.loads(PACKET.read_text())
for name in ['state', 'inputs', 'plan', 'proposal', 'bundle_manifest']: check(packet[name])
manifest = json.loads(Path(packet['bundle_manifest']['path']).read_text())
require(len(manifest) == 23, 'author file count')
for item in manifest:
    check(dict(item, path=str(Path(packet['bundle_manifest']['path']).parent / item['path'])))
plan = json.loads(Path(packet['plan']['path']).read_text())
require(plan['counts'] == dict(custom=95, Foundation=95, artifacts=380,
    external=38, external_companions=114, fresh_prerequisites=0), 'scope')
for pin in plan['pins']: check(pin)
modules = {x['module']: x for x in plan['modules']}
boundary = {x['module'] for x in plan['external']}
visited, edges, active = set(), set(), set()
def visit(name):
    if name not in modules:
        require(name in boundary, 'unknown import ' + name)
        edges.add(name); return
    if name in visited: return
    require(name not in active, 'cycle ' + name); active.add(name)
    item = modules[name]
    check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'imports ' + name)
    for obj in item['objects']: check(obj)
    for dep in item['imports']: visit(dep)
    active.remove(name); visited.add(name)
for name in plan['direct_imports']: visit(name)
require(visited == set(modules) and edges == boundary, 'exact closure')
for item in plan['external']:
    check(item['source'])
    for obj in item['artifacts']: check(obj)
for rec in packet['records']:
    require(rec['exit_code'] == 0, 'author failure')
    for name in ['source','snapshot','log','timing','object']: check(rec[name])
require(imports(packet['records'][0]['source']['path']) == ['Init', *plan['direct_imports']], 'main imports')
require(imports(packet['records'][1]['source']['path']) == ['Init', packet['records'][0]['module']], 'check imports')
check(plan['compiler'])
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'reserve')
private = Path(tempfile.mkdtemp(prefix='arithmetic-pell-recurrence-peer-'))
lib = private / 'lib'; logs = private / 'logs'; lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__, private / 'driver.py')
shutil.copyfile(PACKET, private / 'author-packet.json')
shutil.copyfile(packet['plan']['path'], private / 'plan.json')
for item in plan['modules']:
    folder = lib / Path(item['module'].replace('.', '/')).parent
    folder.mkdir(parents=True, exist_ok=True)
    for obj in item['objects']:
        (folder / Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path = [str(lib), *plan['boundary_search']]
inputs = dict(author_packet=record(PACKET), plan=packet['plan'], compiler=plan['compiler'],
    counts=plan['counts'], sources=[r['source'] for r in packet['records']],
    LEAN_PATH=lean_path, observations=list(observations.values()))
save(private / 'inputs.json', inputs)
state = dict(status='RUNNING', private=str(private), driver=record(__file__),
    inputs=record(private / 'inputs.json'), records=[])
save(private / 'state.json', state)
Path('/tmp/arithmetic-pell-recurrence-peer-latest').write_text(str(private)+'\n')
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
print('PRIVATE ' + str(private), flush=True)
try:
    for author in packet['records']:
        source = author['source']; check(source)
        require(shutil.disk_usage(private).free >= 512*1024**2, 'command reserve')
        short = author['module'].split('.')[-1]
        output = lib / (author['module'].replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        require(not output.exists() and not output.is_symlink(), 'fresh output')
        log = logs / (short + '.log'); timing = logs / (short + '.time')
        snapshot = logs / (short + '.lean'); shutil.copyfile(source['path'], snapshot)
        command = [plan['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
                   '-o', str(output), source['path']]
        print('START '+short, flush=True); start = time.monotonic()
        with log.open('w') as stream:
            code = subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],
                cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
        rec = dict(module=author['module'], source=source, snapshot=record(snapshot),
            command=command, exit_code=code, seconds=time.monotonic()-start,
            log=record(log), timing=record(timing))
        state['records'].append(rec); save(private / 'state.json',state)
        print(log.read_text(), flush=True)
        require(code == 0, 'compile '+short)
        require(not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()), 'clean diagnostics')
        reports = [list(x) for x in re.findall(
            r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())]
        require(reports == author['axiom_reports'], 'exact author reports')
        for name, axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*',axioms)) <=
                {'propext','Classical.choice','Quot.sound'}, 'standard axioms '+name)
        require(output.is_file() and not output.is_symlink(), 'regular output')
        obj = record(output)
        require(obj['sha256'] == author['object']['sha256'], 'author object equality')
        rec.update(object=obj, axiom_reports=reports, matches_author=True)
        save(private / 'state.json',state); check(source)
    for pin in list(observations.values()): check(pin)
    require(shutil.disk_usage(private).free >= 512*1024**2, 'final reserve')
    state.update(status='PASS', final_free_bytes=shutil.disk_usage(private).free,
                 observation_count=len(observations))
    save(private / 'state.json',state)
    print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error)); save(private / 'state.json',state)
    raise
