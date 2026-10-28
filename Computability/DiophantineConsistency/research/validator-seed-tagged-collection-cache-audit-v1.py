"""Read-only Collection prerequisite audit: no compiler, overlay or cache writes."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'research/validator-seed-tagged-collection-cache-plan.json'
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


def check_manifest(path, expected):
    observe(path, expected)
    for item in read(path):
        observe(path.parent / item['path'], item['sha256'])


base_path = REV / 'validator-seed-guarded-comprehension222-cache.json'
root_path = REV / 'validator-seed-guarded-comprehension222-root-replay.json'
observe(base_path, 'ff8d69d0791575a5cc9f63e96d1c1fa90bef24ec92600929f773d6208cace568')
observe(root_path, 'ef51f6203ee7c0376888a1682bc48d7a7c398d7f028531075111d4be8051d424')
base, root = read(base_path), read(root_path)
require(root['status'] == 'PASS', 'Guarded ROOT pair not PASS')
for item in base['inherited_observations'] + base['parent_receipts']:
    observe(item['path'], item['sha256'])
for name in ['compiler', 'manifest', 'toolchain']:
    observe(base[name], base[name + '_sha256'])
check_manifest(REV / 'validator-seed-guarded-comprehension222-root-replay/FILES.json',
               '4c4abe69d3c3614ed285addc3502ded78203bf060a3202ea8d12f6ca177bdd2b')
observe(REV / 'validator-seed-guarded-comprehension222-root.md')
observe(REV / 'validator-seed-guarded-comprehension222-author.md',
        '55f42112855ff6b4334e01513574e309d08669ce82400fe5603a7972130f8d48')
observe(root['author']['path'], root['author']['sha256'])
author = read(root['author']['path'])
check_manifest(Path(author['bundle']) / 'FILES.json', author['manifest_sha256'])

records = {r['module']: r for r in base['modules']}
guarded = root['records'][0]
require(guarded['module'] == 'ZFCinPA.ValidatorSeedGuardedComprehension222'
        and guarded['exit_code'] == 0, 'wrong Guarded ROOT record')
records[guarded['module']] = {
    'module': guarded['module'], 'source': guarded['source']['path'],
    'source_sha256': guarded['source']['sha256'], 'objects': [guarded['object']],
    'imports': imports(guarded['source']['path']), 'provenance_parent': str(root_path),
    'qualification': 'Accepted independent ROOT provider, selected before this plan freeze.'}

# Only these four existing clients are added. Their complete dependency closure
# below is already in the accepted Guarded base; no Foundation module is added.
extra_names = ['BoundedPAConsistency.TypedTemplateProofCompiler',
               'ZFCinPA.SetPlaceholders', 'ZFCinPA.SetPlaceholderQuotient',
               'ZFCinPA.SetCongruence']
fixed_path = REV / 'fixed-consistency73-root-replay/plan.json'
peer_path = REV / 'foundation-ha-consistency-semantics-peer-replay/inputs.json'
observe(fixed_path)
observe(peer_path)
observe(REV / 'foundation-ha-consistency-semantics-peer.md')
check_manifest(REV / 'foundation-ha-consistency-semantics-peer-replay/FILES.json',
               '31200ae13009325bf6918849b18090ce5df425597a253d839cc83d857902a3fb')
fixed = {r['module']: r for r in read(fixed_path)['modules']}
peer = read(peer_path)
peer_records = {r['module']: r for r in peer['modules']}
for name in extra_names:
    old, accepted = fixed[name], peer_records[name]
    require(name not in records, 'unexpected existing extra: ' + name)
    require(old['source']['path'] == accepted['source'] and
            old['source']['sha256'] == accepted['source_sha256'], 'extra source disagreement')
    require(old['objects'] == accepted['objects'], 'extra object disagreement')
    require(old['actual_imports'] == accepted['imports'], 'extra header disagreement')
    observe(old['provenance']['path'], old['provenance']['sha256'])
    absent = [{'path': p, 'exists_now': Path(p).exists()} for p in old['absent_companions']]
    require(not any(x['exists_now'] for x in absent), 'historically absent companion appeared')
    records[name] = {**old, 'source': old['source']['path'],
                     'source_sha256': old['source']['sha256'],
                     'provenance_parent': str(peer_path),
                     'historical_source_pair_parent': str(fixed_path),
                     'absence_observations': absent,
                     'qualification': 'Source-identical historical pair, reauthenticated by accepted '
                                      'fixed-consistency and consistency-semantics closures; not freshly compiled here.'}

external = {r['module']: r for r in base['external']}
order, seen, visiting, external_names = [], set(), set(), set()


def visit(name):
    if name in seen:
        return
    require(name not in visiting, 'import cycle: ' + name)
    if name not in records:
        require(name in external, 'unrecorded import: ' + name)
        external_names.add(name)
        return
    visiting.add(name)
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
    visiting.remove(name)
    seen.add(name)
    order.append({**record, 'actual_imports': actual})


target_imports = [guarded['module'], 'ZFCinPA.SetCongruence']
for name in target_imports:
    visit(name)
boundaries = [external[name] for name in sorted(external_names)]
paths = [root['private_provider'], peer['lean_path'].split(':')[0]]
paths.extend(p for p in base['lean_path'].split(':')[1:] if p not in paths)
providers, artifact_providers = [], []
for item in order + boundaries:
    name = item['module']
    artifacts = item['objects'] if 'objects' in item else [item]
    for artifact in artifacts:
        filename = Path(artifact['path']).name
        stem = name.split('.')[-1]
        require(filename.startswith(stem + '.'), 'bad artifact name: ' + filename)
        relative = name.replace('.', '/') + filename[len(stem):]
        found = next((Path(p) / relative for p in paths if (Path(p) / relative).is_file()), None)
        require(found is not None, 'missing first artifact provider: ' + relative)
        pin = {'module': name, 'relative': relative, **observe(found, artifact['sha256'])}
        artifact_providers.append(pin)
        if relative.endswith('.olean'):
            providers.append(pin)

counts = {'cached_modules': len(order),
          'foundation': sum(r['module'].startswith('Foundation.') for r in order),
          'artifacts': sum(len(r['objects']) for r in order),
          'external_boundaries': len(boundaries)}
require(counts == {'cached_modules': 207, 'foundation': 136,
                   'artifacts': 615, 'external_boundaries': 45}, 'unexpected closure')
require(len(providers) == 252 and len(artifact_providers) == 660, 'wrong first-provider count')
anchors = [ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC' / (n + '.lean')
           for n in ['KLowerTag', 'KLowerRaw', 'KLowerSeed', 'KLowerRel', 'KLowerEqv',
                     'KLowerQHyp', 'KQHyp', 'KQ1ZF', 'ProfileCollection', 'ProfileComposition']]
anchors += [ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA' / (n + '.lean')
            for n in ['ValidatorSeedGuardedComprehension222', 'ValidatorSeedRawComprehension222',
                      'ValidatorSeedSourceBasis222', 'ValidatorFullSeedTheory222',
                      'ValidatorSourceFullSeed222', 'SetCongruence', 'LSchema', 'InternalInterpretation']]
anchors += [D / 'research/validator-seed-marker-counter-proposal.md',
            D / 'research/validator-seed-tagged-interpretation-plan.md',
            D / 'research/validator-seed-tagged-interpretation-plan.json',
            ROOT / 'Logic/Interpretability/ZFCinPA/set_congruence_refresh.md']
anchor_pins = [observe(p) for p in anchors]
driver = observe(__file__)
result = {
    'status': 'READ_ONLY_PLAN_NO_COMPILER_OR_OVERLAY',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'imports': target_imports, 'counts': counts,
    'new_prerequisite_refresh': [], 'added_cached_clients': extra_names + [guarded['module']],
    'modules_dependency_order': order, 'external': boundaries,
    'actual_first_providers': providers, 'actual_first_artifact_providers': artifact_providers,
    'existing_search_path': paths, 'selected_guarded_provider': records[guarded['module']],
    'compiler': observe(base['compiler'], base['compiler_sha256']),
    'toolchain': observe(base['toolchain'], base['toolchain_sha256']),
    'manifest': observe(base['manifest'], base['manifest_sha256']),
    'anchor_sources': anchor_pins, 'driver': driver,
    'parents': [observe(p) for p in [base_path, root_path, fixed_path, peer_path]],
    'observations': [{'path': p, 'sha256': h} for p, h in sorted(observations.items())],
    'scope': 'Read-only current source/header/provider authentication for a proposed two-leaf '
             'Collection packet. No Lean invocation, overlay, dependency refresh or cache mutation. '
             'Guarded selects accepted ROOT. Four historical extra objects retain exact original '
             'proof-run and absent-companion qualifications. No claim of a fresh entire closure.'}
require(not OUT.exists(), 'refuse to overwrite frozen inventory')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'output': str(OUT), 'sha256': sha(OUT), 'counts': counts,
                  'observations': len(observations), 'artifact_providers': len(artifact_providers)}, indent=2))
