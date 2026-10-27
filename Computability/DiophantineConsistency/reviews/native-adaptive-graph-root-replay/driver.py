from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PACKET = DC / 'reviews/native-adaptive-graph-replay.json'
EXPECTED_PACKET = '2f86c7800877ec5f25ccf9662dd55451761eb9502690196501bb048e0de4779d'
NAMES = ['DiophantineConsistency.NativeAdaptiveGraph',
         'DiophantineConsistency.NativeAdaptiveGraphChecks']
observations = []

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def record(path):
    p = Path(path)
    b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

def pin(x):
    actual = record(x['path'])
    require(actual['sha256'] == x['sha256'], 'hash ' + x['path'])
    if 'bytes' in x:
        require(actual['bytes'] == x['bytes'], 'size ' + x['path'])
    observations.append(actual)

def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')

def imports(path):
    s = Path(path).read_text()
    out, i, depth = [], 0, 0
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; i += 2
            elif pair == '-/':
                depth -= 1; i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; i += 2
        elif pair == '--':
            while i < len(s) and s[i] != '\n':
                i += 1
        else:
            out.append(s[i]); i += 1
    require(depth == 0, 'comment balance')
    result, header = ['Init'], True
    for line in ''.join(out).splitlines():
        t = line.strip()
        if not t:
            continue
        m = re.fullmatch(r'import\s+([A-Za-z_][A-Za-z_0-9. ]*)', t)
        if m:
            require(header, 'late import ' + str(path))
            result.extend(m.group(1).split())
        else:
            header = False
    return list(dict.fromkeys(result))

pin(dict(path=str(PACKET), sha256=EXPECTED_PACKET))
packet = json.loads(PACKET.read_text())
for key in ['driver', 'inputs', 'state', 'finite_binding', 'auditor',
            'normal_stdout', 'optimized_stdout', 'bundle_manifest']:
    pin(packet[key])
manifest = Path(packet['bundle_manifest']['path'])
files = json.loads(manifest.read_text())
require(len(files) == 51, 'author manifest count')
for item in files:
    pin(dict(item, path=str(manifest.parent / item['path'])))
inputs = json.loads(Path(packet['inputs']['path']).read_text())
for item in inputs['pins']:
    pin(item)
pin(inputs['compiler'])
custom = {x['module']: x for x in inputs['selected_custom']}
external = {x['module']: x for x in inputs['external_boundary']}
require(len(custom) == 35 and len(external) == 22, '35/22 scope')
require(sum(len(x['artifacts']) for x in external.values()) == 66, '66 companions')
require(not set(custom) & set(NAMES), 'new leaves are absent from cache')
for item in custom.values():
    pin(item['source']); pin(item['object'])
    require(imports(item['source']['path']) == item['actual_imports'], 'custom header ' + item['module'])
    require(set(item['actual_imports']) <= set(custom) | set(external), 'closed custom imports')
for item in external.values():
    pin(item['source'])
    for obj in item['artifacts']:
        pin(obj)
sources = inputs['sources']
require([s['module'] for s in sources] == NAMES, 'exact two leaves')
require(imports(sources[0]['path']) == ['Init', 'DiophantineConsistency.NativeAdaptiveSourceRestoration',
        'DiophantineConsistency.NativeAdaptiveUnitFactors'], 'main header')
require(imports(sources[1]['path']) == ['Init', NAMES[0]], 'checks header')
for source in sources:
    pin(source)
binding = json.loads(Path(packet['finite_binding']['path']).read_text())
require(binding['status'] == 'PASS', 'author literal audit')
for key in ['graph', 'source', 'checks', 'auditor']:
    pin(binding[key])
require(shutil.disk_usage('/tmp').free >= 512 * 1024**2, 'initial reserve')
private = Path(tempfile.mkdtemp(prefix='native-adaptive-graph-root-'))
lib = private / 'lib'; logs = private / 'logs'
lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__, private / 'driver.py')
save(private / 'INPUTS.json', inputs)
for item in custom.values():
    target = lib / (item['module'].replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(Path(item['object']['path']).resolve())
lean_path = [str(lib), *inputs['LEAN_PATH'][1:]]
state = dict(status='RUNNING', scope='35 cached custom/22 boundary/66 companions; two fresh leaves only',
             private=str(private), driver=record(__file__), author_packet=record(PACKET),
             inputs=record(private / 'INPUTS.json'), LEAN_PATH=lean_path, records=[])
save(private / 'ROOT.json', state)
Path('/tmp/native-adaptive-graph-root-latest').write_text(str(private) + '\n')
print('PRIVATE ' + str(private), flush=True)
try:
    # Copy the inert auditor and its entire four-file input set. Its parents[2]
    # root now resolves privately, so frozen author certificates are never written.
    mapping = {}
    for key in ['graph', 'source', 'checks', 'auditor']:
        source = Path(binding[key]['path'])
        target = private / 'literal' / source.relative_to(DC)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        require(record(target)['sha256'] == binding[key]['sha256'], 'private literal copy')
        mapping[key] = str(target)
    syntax = []
    for flags, label in [([], 'normal'), (['-O'], 'optimized')]:
        command = ['/usr/bin/python3', *flags, mapping['auditor']]
        log = logs / ('syntax-' + label + '.stdout')
        with log.open('w') as f:
            code = subprocess.run(command, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT).returncode
        require(code == 0, 'syntax ' + label)
        certificate = Path(mapping['auditor']).with_name('BINDING.json')
        snapshot = logs / ('syntax-' + label + '.json')
        shutil.copyfile(certificate, snapshot)
        result = json.loads(snapshot.read_text())
        for key in ['status', 'scope', 'aliases', 'rows', 'fields', 'rejected_mutations', 'counts']:
            require(result[key] == binding[key], 'same literal field ' + key)
        for key in ['graph', 'source', 'checks', 'auditor']:
            require(result[key]['sha256'] == binding[key]['sha256'] and
                    result[key]['bytes'] == binding[key]['bytes'], 'same literal input ' + key)
        syntax.append(dict(label=label, command=command, exit_code=code,
                           stdout=record(log), certificate=record(snapshot)))
    require(Path(syntax[0]['stdout']['path']).read_bytes() == Path(syntax[1]['stdout']['path']).read_bytes(), 'normal/O stdout')
    require(Path(syntax[0]['certificate']['path']).read_bytes() == Path(syntax[1]['certificate']['path']).read_bytes(), 'normal/O certificate')
    state['syntax'] = dict(mapping=mapping, runs=syntax, counts=binding['counts'])
    save(private / 'ROOT.json', state)
    env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH', None)
    for source, expected, author in zip(sources, [0, 8], packet['records']):
        require(shutil.disk_usage(private).free >= 512 * 1024**2, 'before compile reserve')
        pin(source)
        module = source['module']; short = module.split('.')[-1]
        output = lib / (module.replace('.', '/') + '.olean')
        require(not output.exists() and not output.is_symlink(), 'fresh new output')
        snapshot = logs / (short + '.lean')
        shutil.copyfile(source['path'], snapshot)
        log = logs / (short + '.log'); timing = logs / (short + '.time')
        command = [inputs['compiler']['path'], '-M6000', '-j1', '-DElab.async=false',
                   '-o', str(output), source['path']]
        print('START ' + short, flush=True)
        start = time.monotonic()
        with log.open('w') as f:
            code = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                                  cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
        entry = dict(module=module, source=source, snapshot=record(snapshot), command=command,
                     exit_code=code, seconds=time.monotonic()-start, log=record(log), timing=record(timing))
        state['records'].append(entry); save(private / 'ROOT.json', state)
        print(log.read_text(), flush=True)
        require(code == 0, 'compile ' + module)
        require(not re.search(r'\b(?:warning|error|sorryAx)\b', log.read_text()), 'clean diagnostics')
        reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log.read_text())
        require(len(reports) == expected, 'report count')
        for name, axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'standard axioms ' + name)
        require(output.is_file() and not output.is_symlink(), 'regular fresh output')
        entry.update(object=record(output), axiom_reports=reports)
        require(entry['object']['sha256'] == author['object']['sha256'], 'byte-identical object')
        pin(author['object'])
        require(reports == [tuple(x) for x in author['axiom_reports']], 'same reports')
        require(log.read_bytes() == Path(author['log']['path']).read_bytes(), 'same logs')
        save(private / 'ROOT.json', state)
    for observation in list(observations):
        pin(observation)
    require(shutil.disk_usage(private).free >= 512 * 1024**2, 'final reserve')
    save(private / 'OBSERVATIONS.json', observations)
    state.update(status='PASS', observations=record(private / 'OBSERVATIONS.json'),
                 observation_count=len(observations), unique_pins=len({x['path'] for x in observations}),
                 final_free_bytes=shutil.disk_usage(private).free)
    save(private / 'ROOT.json', state)
    print('PASS ' + str(private), flush=True)
except BaseException as error:
    state.update(status='FAILED', failure=str(error)); save(private / 'ROOT.json', state)
    raise
