from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PACKET = DC / 'reviews/arithmetic-dag-controlperm222-replay.json'
MF = DC / 'reviews/arithmetic-dag-controlperm222-author-replay/FILES.json'
observations = []

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def record(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

def check(x):
    actual = record(x['path'])
    require(actual['sha256'] == x['sha256'], 'hash ' + x['path'])
    if 'bytes' in x:
        require(actual['bytes'] == x['bytes'], 'size ' + x['path'])
    observations.append(actual)

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
    require(depth == 0, 'balanced comments')
    return list(dict.fromkeys(['Init'] + [n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', ''.join(out), re.M)
        for n in line.split()]))

check(dict(path=str(PACKET), sha256='979d525f3e40b6d7037b3ee3b8ad210fbfc64410ed5183c7fcedc02f6d22cc4b'))
check(dict(path=str(MF), sha256='1889feb1bcfad0035b58fe8277ac9c794e6037473a791ee1465c90310860f80b'))
packet = json.loads(PACKET.read_text())
files = json.loads(MF.read_text()); require(len(files) == 66, '66-file author manifest')
for item in files:
    check(dict(item, path=str(MF.parent / item['path'])))
check(packet['final_inputs']); check(packet['driver'])
inputs = json.loads(Path(packet['final_inputs']['path']).read_text())
require(inputs['counts'] == dict(custom=138, Foundation=95, reuse=137, artifacts=422,
    fresh_unchanged=1, external=39), 'scope138/95/137/422/1/39')
for pin in inputs['pins']:
    check(pin)
modules = {x['module']: x for x in inputs['modules']}
external = {x['module'] for x in inputs['external']}
require(len(modules) == 138 and len(external) == 39, 'unique inventory')
fresh = 'BusyBeaver.ZFC.PackedTables'
require({n for n,m in modules.items() if not m.get('objects')} == {fresh}, 'one explicit refresh')
require(sum(len(m.get('objects',[])) for m in modules.values()) == 422, '422 artifacts')
visited, used, active = set(), set(), set()
def visit(name):
    if name not in modules:
        require(name in external, 'unknown import ' + name); used.add(name); return
    if name in visited:
        return
    require(name not in active, 'cycle'); active.add(name)
    item = modules[name]
    check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'current header ' + name)
    for obj in item.get('objects',[]):
        check(obj)
    for dependency in item['imports']:
        visit(dependency)
    active.remove(name); visited.add(name)
for name in ['BusyBeaver.ZFC.ArithmeticDagLoops',fresh]:
    visit(name)
require(visited == set(modules) and used == external, 'exact closed DAG')
for entry in inputs['external']:
    if 'path' in entry:
        check(entry)
    else:
        check(entry['object']); check(entry['observed_source'])
        for pin in entry['companions']: check(pin)
records = packet['records']
names = [fresh,'BusyBeaver.ZFC.ArithmeticDagControlPerm222','BusyBeaver.ZFC.ArithmeticDagControlPerm222Checks']
require([r['module'] for r in records] == names, 'three exact fresh records')
for row in records:
    require(row['exit_code'] == 0, 'author pass')
    for key in ['source','snapshot','object','log','timing']:
        check(row[key])
require(imports(records[1]['source']['path']) == ['Init','BusyBeaver.ZFC.ArithmeticDagLoops',fresh], 'main imports')
require(imports(records[2]['source']['path']) == ['Init',names[1]], 'Checks imports')
literal = json.loads(Path('/tmp/dag-controlperm222-root-literal.json').read_text())
require(literal['status'] == 'PASS_FULL_LITERAL' and literal['complete_slot_count'] == 4751 and
        literal['no_high_bits'] and literal['dual_construction_equal'], 'full literal audit')
require(literal['source']['sha256'] == records[1]['source']['sha256'], 'audited actual main')
for pin in literal['sources']:
    check(pin)
check(literal['source']); check(literal['script'])
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'initial reserve')
private = Path(tempfile.mkdtemp(prefix='arithmetic-dag-controlperm222-root-'))
lib = private / 'lib'; logs = private / 'logs'; lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__, private / 'driver.py')
shutil.copyfile(packet['final_inputs']['path'], private / 'inputs.json')
shutil.copyfile('/tmp/dag-controlperm222-root-literal.json', private / 'literal.json')
shutil.copyfile(literal['script']['path'], private / 'literal.py')
for name,item in modules.items():
    folder = lib / Path(name.replace('.','/')).parent; folder.mkdir(parents=True,exist_ok=True)
    for obj in item.get('objects',[]):
        (folder / Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path = [str(lib), *inputs['lean_path'].split(':')[1:]]
state = dict(status='RUNNING', private=str(private), driver=record(__file__),
    author_packet=record(PACKET), counts=inputs['counts'], LEAN_PATH=lean_path, records=[])
save(private / 'ROOT.json',state)
Path('/tmp/arithmetic-dag-controlperm222-root-latest').write_text(str(private)+'\n')
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1'); env.pop('LEAN_SRC_PATH',None)
print('PRIVATE '+str(private),flush=True)
try:
    for author, count in zip(records,[0,0,12]):
        source = author['source']; check(source)
        require(shutil.disk_usage(private).free >= 512*1024**2, 'before command reserve')
        output = lib / (author['module'].replace('.','/')+'.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        require(not output.exists() and not output.is_symlink(),'fresh regular output')
        short = author['module'].split('.')[-1]
        log = logs/(short+'.log'); timing = logs/(short+'.time'); snapshot = logs/(short+'.lean')
        shutil.copyfile(source['path'],snapshot)
        command = [inputs['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),source['path']]
        print('START '+short,flush=True); start = time.monotonic()
        with log.open('w') as stream:
            code = subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,
                env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
        row = dict(module=author['module'],source=source,snapshot=record(snapshot),command=command,
            exit_code=code,seconds=time.monotonic()-start,log=record(log),timing=record(timing))
        state['records'].append(row); save(private/'ROOT.json',state)
        print(log.read_text(),flush=True)
        require(code == 0,'compile '+short)
        require(not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()),'clean diagnostics')
        reports = [list(x) for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())]
        require(len(reports) == count and reports == author['axiom_reports'],'exact report equality')
        for name, axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*',axioms)) <= {'propext','Classical.choice','Quot.sound'},'standard axioms '+name)
        require(output.is_file() and not output.is_symlink(),'regular new output')
        row.update(object=record(output),axiom_reports=reports)
        require(row['object']['sha256'] == author['object']['sha256'],'matching object bytes')
        require(log.read_bytes() == Path(author['log']['path']).read_bytes(),'matching logs')
        check(source); save(private/'ROOT.json',state)
        print('PASS '+short+' '+str(row['seconds']),flush=True)
    for pin in list(observations): check(pin)
    require(shutil.disk_usage(private).free >= 512*1024**2, 'final reserve')
    save(private/'OBSERVATIONS.json',observations)
    state.update(status='PASS',observation_count=len(observations),
        unique_paths=len({x['path'] for x in observations}),final_free_bytes=shutil.disk_usage(private).free)
    save(private/'ROOT.json',state); print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error));save(private/'ROOT.json',state);raise
