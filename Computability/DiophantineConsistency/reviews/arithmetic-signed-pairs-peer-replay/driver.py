from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PACKET = DC / 'reviews/arithmetic-signed-pairs-replay.json'
observations = {}
comparison_count=0

def record(path):
    path = Path(path); data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))

def require(ok, message):
    if not ok: raise RuntimeError(message)

def check(pin):
    global comparison_count
    comparison_count+=1
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
    clean = ''.join(out)
    initial = [] if re.search(r'^\s*prelude\s*$',clean,re.M) else ['Init']
    return list(dict.fromkeys(initial + [n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', clean, re.M)
        for n in line.split()]))

# Separately pin the outer packet and receipt, deliberately outside its manifest.
check(dict(path=str(PACKET), sha256='873e43650bf005b692e3eacbf27732a41d0f0f07c9b806b061b67ee89b33ea87'))
packet=json.loads(PACKET.read_text())
require(packet['status']=='PASS','frozen author PASS')
for key in ['final_state','inputs','providers','authentication','freeze_authentication','plan','scope_supplement','compiler','driver','manifest']: check(packet[key])
receipt=DC/'reviews/arithmetic-signed-pairs-author.md'
check(dict(path=str(receipt),sha256='a0b189809d5f96551541658cbf91a72b383275617f6395c37b2fc557499c37f3'))
manifest_path=DC/'reviews/arithmetic-signed-pairs-author-replay/FILES.json'
check(dict(path=str(manifest_path),sha256='66b4e7a95c1904ce7476fd5159669e68b6803d10f034cf14dd95352275e41751'))
manifest=json.loads(manifest_path.read_text())
require(len(manifest)==25,'complete author manifest')
for item in manifest: check(dict(item,path=str(ROOT/item['path'])))
freeze=json.loads(Path(packet['freeze_authentication']['path']).read_text())
require(freeze['count']==4699 and len(freeze['observations'])==4699,'all author freeze observations')
for observation in freeze['observations']:
    require(observation['expected']['sha256']==observation['actual']['sha256'],'historical comparison')
    check(observation['actual'])
PLAN=DC/'research/arithmetic-negative-norms-cache-plan.json'
check(dict(path=str(PLAN),sha256='366c96fcd290d5b62b493d948f643aa96abc2889f5d9b967085a2ed9541ac8b2'))
SCOPE=DC/'research/arithmetic-signed-pairs-proposal.md'
check(dict(path=str(SCOPE),sha256='35e862bc23920518f5968e10ba1284594d73020a77c4a9ba588d933f426d85ba'))
plan=json.loads(PLAN.read_text())
require(plan['counts']==dict(custom=86,Foundation=86,artifacts=344,external=37,
    boundary_artifacts=111,boundary_primaries=37,boundary_companions=74,
    actual_first_providers=455,fresh_prerequisites=0),'scope')
for pin in plan['pins']: check(pin)
plan_manifest=DC/'research/arithmetic-negative-norms-plan-FILES.json'
check(dict(path=str(plan_manifest),sha256='b2911a36db50876ed15b6550a9d7199329333d79264470da3a1401f3c1113dda'))
for pin in json.loads(plan_manifest.read_text()):
    path=Path(pin['path']); base=ROOT if path.parts[0] in ['Logic','Computability'] else plan_manifest.parent
    check(dict(pin,path=str(base/path)))
# Authenticate every terminal author attempt, retaining its historical source binding.
author_dirs=[Path('/tmp/arithmetic-signed-pairs-author-cto4nnhl'),
             Path('/tmp/arithmetic-signed-pairs-author-kshji581')]
author_states=[]
for number,folder in enumerate(author_dirs):
    attempt=packet['attempts'][number]
    require(attempt['private']==str(folder),'author directory binding')
    state_pin=check(attempt['state']); check(attempt['durable'])
    require(state_pin['sha256']==attempt['durable']['sha256'],'durable state binding')
    st=json.loads((folder/'state.json').read_text())
    require(st['status']==(['FAILED','PASS'][number]),'author chronology')
    check(st['driver']); check(st['inputs'])
    inp=json.loads(Path(st['inputs']['path']).read_text())
    source_map={s['path']:s['snapshot']['path'] for s in inp['sources']}
    for source in inp['sources']:
        check(dict(source,path=source_map[source['path']]))
        check(source['snapshot'])
    for key in ['profile_reference','scope','providers','authentication','compiler']: check(inp[key])
    auth=json.loads(Path(inp['authentication']['path']).read_text())
    for pin in auth['pins']:
        check(dict(pin,path=source_map.get(pin['path'],pin['path'])))
    providers=json.loads(Path(inp['providers']['path']).read_text())
    require(len(providers)==455,'all author providers')
    for item in providers: check(item['actual']); check(item['expected'])
    for row in st['records']:
        require(row['source']['sha256']==row['snapshot']['sha256'],'historical source binding')
        for key in ['snapshot','log','timing']: check(row[key])
        if 'object' in row: check(row['object'])
    author_states.append(state_pin)
final=json.loads((author_dirs[-1]/'state.json').read_text())
require(len(final['records'])==2 and len(final['records'][1]['axiom_reports'])==7,'two leaves seven audits')
# The final state, packet records, and exact source pins must agree.
records=final['records']
require(records==packet['records'],'packet/final record equality')
require([r['source']['sha256'] for r in records]==[
    '802f596f97526763820fb8bb4cd0f6619b2544eae7039577bc9f37bcb6d435a2',
    '20d97e341976602819778ff4b790e559cbe01071f576d8e84fff25251d462baa'],'final source pins')
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
for rec in records:
    require(rec['exit_code'] == 0, 'author failure')
    for name in ['source','snapshot','log','timing','object']: check(rec[name])
require(imports(records[0]['source']['path']) == ['Init', *plan['direct_imports']], 'main imports')
require(imports(records[1]['source']['path']) == ['Init', records[0]['module']], 'check imports')
check(plan['compiler'])
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'reserve')
private = Path(tempfile.mkdtemp(prefix='arithmetic-signed-pairs-peer-'))
lib = private / 'lib'; logs = private / 'logs'; lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__, private / 'driver.py')
shutil.copyfile(PACKET, private / 'author-packet.json')
# Immutable plan/proposal/author references are pinned without copying large inventories.
for item in plan['modules']:
    folder = lib / Path(item['module'].replace('.', '/')).parent
    folder.mkdir(parents=True, exist_ok=True)
    for obj in item['objects']:
        (folder / Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path = [str(lib), *plan['boundary_search']]
require(all('/.lake/packages/' in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for p in lean_path[1:]),'package-only fallback')
providers=[]
for item in plan['modules'] + plan['external']:
    objs = item.get('objects', item.get('artifacts'))
    for expected in objs:
        name = Path(expected['path']).name
        rel = Path(*item['module'].split('.')[:-1]) / name
        actual = next((Path(root)/rel for root in lean_path if (Path(root)/rel).is_file()), None)
        require(actual is not None, 'actual provider absent ' + str(rel))
        require(record(actual)['sha256'] == expected['sha256'], 'actual provider hash ' + str(rel))
        providers.append(dict(module=item['module'],actual=check(dict(expected,path=str(actual))),expected=expected))
require(len(providers)==455, 'all actual providers')
save(private/'providers.json',providers)
inputs = dict(author_packet=record(PACKET), plan=record(PLAN), scope=record(SCOPE), author_receipt=record(receipt), author_states=author_states, compiler=plan['compiler'],
    counts=plan['counts'], author_manifest=record(manifest_path), providers=record(private/'providers.json'), sources=[r['source'] for r in records],
    LEAN_PATH=lean_path, observations=list(observations.values()))
save(private / 'inputs.json', inputs)
state = dict(status='RUNNING', private=str(private), driver=record(__file__),
    inputs=record(private / 'inputs.json'), records=[])
save(private / 'state.json', state)
with Path('/tmp/arithmetic-signed-pairs-peer-runs.txt').open('a') as stream: stream.write(str(private)+'\n')
Path('/tmp/arithmetic-signed-pairs-peer-latest').write_text(str(private)+'\n')
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
# Preserve BOTH inputs before the first compiler, even if the main fails.
for row in records:
    shutil.copyfile(row['source']['path'],logs/(row['module'].split('.')[-1]+'.lean'))
print('PRIVATE ' + str(private), flush=True)
try:
    for author in records:
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
        require(rec['log']['sha256'] == author['log']['sha256'], 'author log equality')
        rec.update(object=obj, axiom_reports=reports, matches_author=True)
        save(private / 'state.json',state); check(source)
    for pin in list(observations.values()): check(pin)
    require(shutil.disk_usage(private).free >= 512*1024**2, 'final reserve')
    state.update(status='PASS', final_free_bytes=shutil.disk_usage(private).free,
                 observation_count=len(observations),comparison_count=comparison_count)
    save(private / 'state.json',state)
    print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error)); save(private / 'state.json',state)
    raise
