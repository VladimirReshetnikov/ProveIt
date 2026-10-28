"""Read-only current-source/provider audit; no compiler, overlay, or cache writes."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'research/validator-seed-guarded-comprehension-cache-plan.json'
observations = {}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def observe(path, expected=None):
    path = str(path)
    actual = sha(path)
    require(expected is None or actual == expected, 'hash drift: ' + path)
    require(path not in observations or observations[path] == actual,
            'mid-audit drift: ' + path)
    observations[path] = actual
    return {'path': path, 'sha256': actual}


def imports(path):
    source = Path(path).read_text()
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and source.startswith('--', i):
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            out.extend(' ' * (j - i))
            i = j
        else:
            out.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    require(depth == 0, 'unclosed comment: ' + str(path))
    source = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', source, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', source, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))


base_path = REV / 'validator-seed-raw-comprehension222-cache.json'
replay_path = REV / 'validator-seed-raw-comprehension222-replay.json'
observe(base_path, '4f8bc557fe69b298526859717182a1d6e557fe8d934420fb0ac98e0c66343c24')
observe(replay_path, 'e78586fcd4571a9efd18c7e908339b3f18dc901594371b77702896f8e2b09fe1')
base, replay = read(base_path), read(replay_path)
require(replay['status'] == 'PASS', 'Raw author pair not PASS')
for item in base['inherited_observations'] + base['parent_receipts']:
    observe(item['path'], item['sha256'])
for name in ['compiler', 'manifest', 'toolchain']:
    observe(base[name], base[name + '_sha256'])
bundle = Path(replay['bundle'])
observe(bundle / 'FILES.json', replay['manifest_sha256'])
for item in read(bundle / 'FILES.json'):
    observe(bundle / item['path'], item['sha256'])
observe(REV / 'validator-seed-raw-comprehension222-author.md',
        '9721335981a637099a6d1cd8fb9a2511e8d98df23e08ba786d117d5922ffda88')

records = {r['module']: r for r in base['modules']}
raw = replay['completed'][0]
require(raw['module'] == 'ZFCinPA.ValidatorSeedRawComprehension222' and raw['exit_code'] == 0,
        'wrong fresh Raw record')
records[raw['module']] = {
    'module': raw['module'], 'source': raw['source'], 'source_sha256': raw['source_sha256'],
    'objects': [raw['object']], 'imports': imports(raw['source']),
    'provenance_parent': str(replay_path),
    'qualification': 'Frozen author PASS only; root independent acceptance pending at plan freeze.'}
external = {r['module']: r for r in base['external']}
order, seen, external_names = [], set(), set()


def visit(name):
    if name in seen:
        return
    if name not in records:
        require(name in external, 'unrecorded import: ' + name)
        external_names.add(name)
        return
    seen.add(name)
    record = records[name]
    observe(record['source'], record['source_sha256'])
    actual = imports(record['source'])
    require(set(actual) == set(record.get('actual_imports', record['imports'])),
            'header drift: ' + name)
    for dependency in actual:
        visit(dependency)
    for item in record['objects']:
        observe(item['path'], item['sha256'])
    for key in ['provenance', 'trace', 'lake_trace']:
        item = record.get(key)
        if isinstance(item, dict) and 'path' in item and 'sha256' in item:
            observe(item['path'], item['sha256'])
    order.append({**record, 'actual_imports': actual})


visit(raw['module'])
boundaries = [external[name] for name in sorted(external_names)]
paths = base['lean_path'].split(':')
paths.append(str(Path(base['compiler']).parent.parent / 'lib/lean'))
providers = []
for item in order + boundaries:
    name = item['module']
    if 'objects' in item:
        expected = next(x['sha256'] for x in item['objects'] if x['path'].endswith('.olean'))
    else:
        expected = item['sha256']
        observe(item['path'], expected)
    matches = [Path(p) / (name.replace('.', '/') + '.olean') for p in paths]
    found = next((p for p in matches if p.is_file()), None)
    require(found is not None, 'missing first provider: ' + name)
    providers.append({'module': name, **observe(found, expected)})
counts = {'cached_modules': len(order),
          'foundation': sum(r['module'].startswith('Foundation.') for r in order),
          'artifacts': sum(len(r['objects']) for r in order),
          'external_boundaries': len(boundaries)}
require(counts == {'cached_modules': 202, 'foundation': 136,
                   'artifacts': 610, 'external_boundaries': 45}, 'unexpected closure')
anchors = [ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC' / (n + '.lean')
           for n in ['KLowerRaw', 'KLowerTag', 'KLowerRel', 'KLowerSeed']]
anchors += [ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA' / (n + '.lean')
            for n in ['ValidatorSeedRawComprehension222', 'ValidatorSeedSourceBasis222',
                      'ValidatorFullSeedTheory222', 'ValidatorSourceFullSeed222']]
result = {
    'status': 'READ_ONLY_PLAN_NO_COMPILER_OR_OVERLAY',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'imports': [raw['module']], 'counts': counts,
    'modules_dependency_order': order, 'external': boundaries,
    'actual_first_providers': providers, 'existing_search_path': paths,
    'raw_provider_status': records[raw['module']]['qualification'],
    'anchor_sources': [observe(p) for p in anchors],
    'driver': observe(__file__),
    'parents': [observe(base_path), observe(replay_path), observe(bundle / 'FILES.json')],
    'observations': [{'path': p, 'sha256': h} for p, h in sorted(observations.items())],
    'scope': 'Read-only reauthentication of exact reused source/header/object and external boundaries. '
             'No Lean invocation, no dependency refresh, no overlay or cache mutation. '
             'Inherited trace and absent-companion qualifications remain explicit. '
             'Raw author provider is provisional until separate root acceptance.'}
require(not OUT.exists(), 'refuse to overwrite frozen inventory')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'output': str(OUT), 'sha256': sha(OUT), 'counts': counts,
                  'observations': len(observations)}, indent=2))
