"""Read-only current-source/provider audit; no compiler, overlay, or cache writes."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'reviews/validator-seed-guarded-comprehension222-provider-supplement.json'
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



plan_path = D / 'research/validator-seed-guarded-comprehension-cache-plan.json'
observe(plan_path, '42822cf5e43a8541d9fabe86b1c031e9c8fe3c64d97ea89a1fa0f540d355cba8')
plan = read(plan_path)
for item in plan['observations']:
    observe(item['path'], item['sha256'])
root_packet = REV / 'validator-seed-raw-comprehension222-root-replay.json'
root_receipt = REV / 'validator-seed-raw-comprehension222-root.md'
root_manifest = REV / 'validator-seed-raw-comprehension222-root-replay/FILES.json'
observe(root_packet, 'eee34d71f8a9ef55a84ba6e711e281f9b388941b59a69d854fbc33000413745e')
observe(root_receipt, 'a7a172bdb317e6309f257a8cc5054ad485f13ba87c436cb8e18150930a4d5973')
observe(root_manifest, '0684def2c890279967b4d3f531452547854da63097e2bcdf18bf65a4667f27c9')
items = read(root_manifest)
require(len(items) == 15, 'root manifest count')
for item in items:
    observe(ROOT / item['path'], item['sha256'])
root = read(root_packet)
require(root['status'] == 'PASS' and root['reports'] == 11, 'root not PASS')
for rec in root['records']:
    require(rec['exit_code'] == 0 and rec['author_object_and_full_log_equal'], 'root record not PASS')
    for key in ['source', 'snapshot', 'log', 'timing', 'object']:
        item = rec[key]
        observe(item['path'], item['sha256'])
records = json.loads(json.dumps(plan['modules_dependency_order']))
raw = next(r for r in records if r['module'] == 'ZFCinPA.ValidatorSeedRawComprehension222')
raw['objects'] = [root['records'][0]['object']]
raw['qualification'] = 'Root accepted after independent fresh pair; exact source, object and full logs match author.'
raw['provenance_parent'] = str(root_packet)
seen = set()
for r in records:
    observe(r['source'], r['source_sha256'])
    actual = imports(r['source'])
    require(actual == r['actual_imports'], 'header/order drift ' + r['module'])
    for dep in actual:
        require(dep in seen or any(e['module'] == dep for e in plan['external']), 'dependency order ' + dep)
    for obj in r['objects']:
        observe(obj['path'], obj['sha256'])
    seen.add(r['module'])
paths = [root['private_provider']] + plan['existing_search_path']
paths = list(dict.fromkeys(paths))
providers = []
for r in records + plan['external']:
    name = r['module']
    expected = next(o['sha256'] for o in r['objects'] if o['path'].endswith('.olean')) if 'objects' in r else r['sha256']
    found = next((Path(p) / (name.replace('.', '/') + '.olean') for p in paths
                  if (Path(p) / (name.replace('.', '/') + '.olean')).is_file()), None)
    require(found is not None, 'missing provider ' + name)
    providers.append({'module': name, **observe(found, expected)})
counts = {'cached_modules': len(records), 'foundation': sum(r['module'].startswith('Foundation.') for r in records),
          'artifacts': sum(len(r['objects']) for r in records), 'external_boundaries': len(plan['external'])}
require(counts == plan['counts'], 'counts changed')
result = {'status': 'ROOT_PROVIDER_AUTHENTICATED_NO_COMPILER_OR_OVERLAY',
          'counts': counts, 'historical_plan': observe(plan_path),
          'root_packet': observe(root_packet), 'root_receipt': observe(root_receipt),
          'root_manifest': observe(root_manifest), 'modules_dependency_order': records,
          'external': plan['external'], 'existing_search_path': paths, 'first_providers': providers,
          'driver': observe(__file__),
          'observations': [{'path': p, 'sha256': h} for p, h in sorted(observations.items())],
          'scope': 'Only Raw main provider selection changes, to the accepted root object. '
                   'Historical provisional plan untouched; all inherited trace and companion qualifications retained. '
                   'No Lean, dependency build, overlay or accepted-source mutation.'}
require(not OUT.exists(), 'frozen output exists')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'counts': counts, 'observations': len(observations)}, indent=2))
