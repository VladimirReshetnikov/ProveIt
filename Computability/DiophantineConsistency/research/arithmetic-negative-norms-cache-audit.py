from pathlib import Path
import hashlib, json, re, shutil

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PARENT = DC / 'research/arithmetic-gcd-normalization-cache-plan.json'
ACCEPTED = DC / 'reviews/arithmetic-gcd-normalization-root-replay.json'
PROPOSAL = DC / 'research/arithmetic-negative-norms-proposal.md'
OUTPUT = DC / 'research/arithmetic-negative-norms-cache-plan.json'
pins = {}; observations = 0


def require(ok, message):
    if not ok: raise RuntimeError(message)


def record(path):
    path = Path(path); data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def check(expected):
    global observations
    actual = record(expected['path'])
    require(actual['sha256'] == expected['sha256'], 'hash '+expected['path'])
    require('bytes' not in expected or actual['bytes'] == expected['bytes'], 'size '+expected['path'])
    pins[actual['path']] = actual; observations += 1
    return actual


def check_nested(value):
    if isinstance(value, dict):
        if 'path' in value and 'sha256' in value: check(value)
        for child in value.values(): check_nested(child)
    elif isinstance(value, list):
        for child in value: check_nested(child)


def imports(path):
    source = Path(path).read_text(); clean = []; index = depth = 0
    while index < len(source):
        pair = source[index:index+2]
        if depth:
            if pair == '/-': depth += 1; index += 2
            elif pair == '-/': depth -= 1; index += 2
            else: clean.append('\n' if source[index] == '\n' else ' '); index += 1
        elif pair == '/-': depth = 1; index += 2
        elif pair == '--':
            while index < len(source) and source[index] != '\n': index += 1
        else: clean.append(source[index]); index += 1
    require(depth == 0, 'comment balance')
    text = ''.join(clean)
    initial = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    return list(dict.fromkeys(initial+[name for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M)
        for name in line.split()]))


require(not OUTPUT.exists(), 'new read-only inventory')
require(shutil.disk_usage('/tmp').free >= 512*1024**2, 'reserve')
check(dict(path=str(PARENT), sha256='1206727b503151356d3ba49f713e09bf88b84d3d6af131ca6a29625e221c2a14'))
check(dict(path=str(ACCEPTED), sha256='b74df44673d2f89c82b6c85237c1e203a03296068dd0f6d455ecf4ad29d14512'))
parent = json.loads(PARENT.read_text()); accepted = json.loads(ACCEPTED.read_text())
require(accepted['status'] == 'PASS', 'accepted root status')
for pin in parent['pins']: check(pin)
check_nested(accepted)
check_nested(json.loads(Path(accepted['final_authentication']['path']).read_text()))
state = json.loads(Path(accepted['state']['path']).read_text())
check(state['inputs']); inputs = json.loads(Path(state['inputs']['path']).read_text())
check_nested(inputs)
check_nested(json.loads(Path(inputs['authentication']['path']).read_text()))
manifest = DC / 'reviews/arithmetic-gcd-normalization-root-replay/FILES.json'
check(dict(path=str(manifest), sha256='b63ead412d73162dce5f37a2605776c3662c779382f45620d96f38831aa5a009'))
for entry in json.loads(manifest.read_text()):
    check(dict(entry, path=str(ROOT/entry['path'])))

modules = {m['module']: m for m in parent['modules']}
boundary = {m['module']: m for m in parent['external']}
visited = set(); active = set(); order = []; used = set()


def visit(name):
    if name not in modules:
        require(name in boundary, 'new external boundary '+name); used.add(name); return
    if name in visited: return
    require(name not in active, 'import cycle '+name); active.add(name)
    item = modules[name]; check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'current header '+name)
    for dep in item['imports']: visit(dep)
    for obj in item['objects']: check(obj)
    active.remove(name); visited.add(name); order.append(name)


direct = ['Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring']
for name in direct: visit(name)
require(visited == set(modules) and used == set(boundary), 'exact narrowed DAG')
external = [boundary[name] for name in sorted(used)]
for item in external:
    check(item['source'])
    for artifact in item['artifacts']: check(artifact)
search = [accepted['private_provider'], *parent['boundary_search']]
providers = []
for item in [modules[name] for name in order]+external:
    for expected in item.get('objects', item.get('artifacts')):
        relative = Path(*item['module'].split('.')[:-1])/Path(expected['path']).name
        actual = next((Path(root)/relative for root in search if (Path(root)/relative).is_file()), None)
        require(actual is not None, 'missing first provider '+str(relative))
        providers.append(dict(module=item['module'], expected=expected,
            actual=check(dict(expected, path=str(actual)))))
counts = dict(custom=len(order), Foundation=sum(n.startswith('Foundation.') for n in order),
    artifacts=sum(len(modules[n]['objects']) for n in order), external=len(external),
    boundary_artifacts=sum(len(x['artifacts']) for x in external), boundary_primaries=len(external),
    boundary_companions=sum(len(x['artifacts'])-1 for x in external),
    actual_first_providers=len(providers), fresh_prerequisites=0)
require(counts == dict(custom=86, Foundation=86, artifacts=344, external=37,
    boundary_artifacts=111, boundary_primaries=37, boundary_companions=74,
    actual_first_providers=455, fresh_prerequisites=0), 'exact requested scope')
guides = []
guide_hashes = {
    'ArithmeticExpression':'19fe455df9e5a2f504af9cddcc4f3af10522c97f11f119e20b64195cf96b7baf',
    'NaturalExpression':'a202ec90e91f2ed35e0aa00394ea94a47d29b32a64704dd7f3ec2c7155c30250',
    'NaturalExpressionSemiring':'a2fdccfa253e93ce72ad0ae5dadfaa9101011a9f5e3a4842fcd3cb2a6ec07dbf',
    'CurrentEquationSyntax2011':'744ed9b68cc2b9d94a8df0d19f5337afb1574ca2ec254dbef66fa11031d2ee7d',
    'ObjectCurrentEquation2011':'ee7f8a8602f69b4952a188ba9fec3ac84bbc798d12a43afd795655bec361e7c3',
    'Carrier65':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154',
    'ShortEquation':'2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68',
    'ShortSystem':'a9d50c6d8268df4d854d056c83995b3e0547c483fd800993471b2c718201d44a',
    'ConsecutivePell':'2ca72494501464fe29aeef854fdbf585b0aba28ba0687df4a6aa8d8095699d92',
    'ArithmeticPellFirstIndex':'86e3a3698a1a78e713e80d876f8ccee0067dd8900854dcf6958cbe78abf96631',
    'ArithmeticPellHalfIndex':'222bc3bd7e7fbb2c4924fee0b26c24f38e359475b956fd800116b1abe665871c',
    'ArithmeticPellPowerRecovery':'a1df92e4dc70697747d4b8e5355b141aa9d544ac9df873cafc7a757de641f562'}
for name, sha in guide_hashes.items():
    guides.append(check(dict(path=str(DC/('Lean/DiophantineConsistency/'+name+'.lean')), sha256=sha)))
check(parent['compiler']); check(record(PROPOSAL)); check(record(__file__))
for pin in list(pins.values()): check(pin)
require(shutil.disk_usage('/tmp').free >= 512*1024**2+2*1024**2, 'output reserve')
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
    scope='ArithmeticNegativeNorms + Checks only: universal mod4 square-discriminant negative-unit exclusion, bounded internal consecutive-product descent and its actual main/strong/aux corollaries. Signed-pair product cancellation and actual splitNatural syntax binding remain later obligations.',
    parent=record(PARENT), accepted_provider_packet=record(ACCEPTED), accepted_provider=accepted['private_provider'],
    proposal=record(PROPOSAL), direct_imports=direct, counts=counts,
    modules=[modules[name] for name in order], topological_order=order, external=external,
    boundary_search=parent['boundary_search'], audited_search=search, first_providers=providers,
    compiler=parent['compiler'], source_guides_not_imports=guides, audit=record(__file__),
    pins=list(pins.values()), observations=observations, unique_paths=len(pins))
OUTPUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(plan=record(OUTPUT), counts=counts, observations=observations,
    unique_paths=len(pins), free_bytes=shutil.disk_usage('/tmp').free), indent=2))
