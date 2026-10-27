"""Read-only provider/header audit for the next finite source-proof leaf.

The only output is a new JSON inventory. No compiler, cache copy, overlay,
dependency build, source mutation, or Git mutation is performed.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'research/validator-seed-raw-comprehension-cache-plan.json'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


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


base_path = REV / 'validator-seed-source-basis222-cache.json'
old_path = D / 'research/validator-seed-tagged-interpretation-plan.json'
peer_path = REV / 'validator-seed-source-basis222-peer-replay.json'
base, old, peer = map(read, [base_path, old_path, peer_path])
require(peer['status'] == 'PASS', 'Basis peer not PASS')
observations = {}


def observe(path, expected=None):
    path = str(path)
    actual = sha(path)
    require(expected is None or actual == expected, 'hash drift: ' + path)
    require(path not in observations or observations[path] == actual, 'mid-audit drift: ' + path)
    observations[path] = actual
    return {'path': path, 'sha256': actual}


for item in base['inherited_observations']:
    observe(item['path'], item['sha256'])
for item in base['parent_receipts']:
    observe(item['path'], item['sha256'])
for name in ['compiler', 'manifest', 'toolchain']:
    observe(base[name], base[name + '_sha256'])
for key in ['author_packet', 'durable_state', 'inputs', 'manifest']:
    item = peer[key]
    observe(item['path'], item['sha256'])
peer_files = read(peer['manifest']['path'])
require(len(peer_files) == peer['files'], 'Basis peer manifest count')
for item in peer_files:
    observe(Path(peer['manifest']['path']).parent / item['path'], item['sha256'])
root_manifest = REV / 'validator-seed-source-basis222-root-auth/FILES.json'
observe(root_manifest, '88780ae02de0f36dc2a790a7097cd11083c70383f10f14695762b01fcf30cb7a')
for item in read(root_manifest):
    observe(root_manifest.parent / item['path'], item['sha256'])

records = {r['module']: r for r in old['branches']['later_parameterized_finite_templates']['modules_dependency_order']}
records.update({r['module']: r for r in base['modules']})
basis = next(r for r in peer['state']['records'] if r['module'] == 'ZFCinPA.ValidatorSeedSourceBasis222')
require(basis['exit_code'] == 0 and basis['object_byte_identical'], 'Basis peer mismatch')
records[basis['module']] = {
    'module': basis['module'], 'source': basis['source']['path'],
    'source_sha256': basis['source']['sha256'], 'objects': [basis['object']],
    'imports': imports(basis['source']['path']), 'provenance_parent': str(peer_path),
    'qualification': 'Independent peer PASS and root accepted at commit a9ee83d2c2; source and object pins unchanged.'}
external = {r['module']: r for r in base['external']}


def branch(targets, optional=False):
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
        previous = record.get('actual_imports', record['imports'])
        require(set(actual) == set(previous) | ({'Init'} if 'Init' in actual else set()), 'header drift: ' + name)
        for dependency in actual:
            visit(dependency)
        for item in record['objects']:
            observe(item['path'], item['sha256'])
        for key in ['provenance', 'trace', 'lake_trace']:
            item = record.get(key)
            if isinstance(item, dict) and 'path' in item and 'sha256' in item:
                observe(item['path'], item['sha256'])
        order.append({**record, 'actual_imports': actual})

    for target in targets:
        visit(target)
    boundaries = [external[name] for name in sorted(external_names)]
    for item in boundaries:
        observe(item['path'], item['sha256'])
    # Select existing paths only; this does not create an overlay or run Lean.
    paths = [peer['private'] + '/lib']
    for record in order:
        primary = next(x for x in record['objects'] if x['path'].endswith('.olean'))
        suffix = record['module'].replace('.', '/') + '.olean'
        require(primary['path'].endswith(suffix), 'primary layout: ' + record['module'])
        paths.append(primary['path'][:-len(suffix)].rstrip('/'))
    paths.extend(base['lean_path'].split(':')[1:])
    paths.append(str(Path(base['compiler']).parent.parent / 'lib/lean'))
    paths = list(dict.fromkeys(paths))
    providers, shadowing = [], []
    for item in order + boundaries:
        name = item['module']
        matches = [Path(p) / (name.replace('.', '/') + '.olean') for p in paths]
        found = next((p for p in matches if p.is_file()), None)
        require(found is not None, 'no first provider: ' + name)
        expected = next(x['sha256'] for x in item['objects'] if x['path'].endswith('.olean')) if 'objects' in item else item['sha256']
        actual_hash = sha(found)
        if actual_hash != expected:
            require(optional, 'recommended provider drift: ' + str(found))
            shadowing.append({'module': name, 'first_path': str(found),
                              'first_sha256': actual_hash, 'selected_sha256': expected})
        providers.append({'module': name, **observe(found), 'matches_selected': actual_hash == expected})
    return {
        'imports': targets, 'optional_not_recommended_for_first_leaf': optional,
        'counts': {'cached_modules': len(order), 'foundation': sum(r['module'].startswith('Foundation.') for r in order),
                   'artifacts': sum(len(r['objects']) for r in order), 'external_boundaries': len(boundaries)},
        'modules_dependency_order': order, 'external': boundaries,
        'proposed_existing_provider_search_path': paths, 'actual_first_providers': providers,
        'shadowing': shadowing,
        'provider_status': 'Exact existing first providers' if not shadowing else
            'Optional records authenticated individually; this broad search path is NOT build-ready. A new selected-only overlay would require separate authorization.'}


branches = {
    'recommended_raw_augmented_template': branch(['ZFCinPA.ValidatorSeedSourceBasis222']),
    'optional_open_template_compiler': branch(['ZFCinPA.ValidatorSeedSourceBasis222', 'ZFCinPA.OpenTemplateClosure'], True)}
anchors = [
    'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/' + name + '.lean'
    for name in ['KLowerRaw', 'KLowerTag', 'KLowerSeed', 'KLowerRel', 'KLowerQHyp', 'KQHyp']]
anchors += ['Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/' + name + '.lean' for name in [
    'ValidatorSourceFullSeed222', 'ValidatorFullSeedTheory222', 'ValidatorSeedSourceBasis222',
    'OpenTemplateClosure', 'OpenSetTemplateCompiler', 'BufferedTemplateProofCompiler', 'SetPlaceholders']]
parents = [base_path, old_path, peer_path, REV / 'validator-seed-source-basis222-author.md',
           REV / 'validator-seed-source-basis222-peer.md',
           REV / 'validator-seed-source-basis222-root.md', root_manifest,
           D / 'research/validator-seed-tagged-interpretation-plan.md']
result = {
    'status': 'READ_ONLY_PLAN_NO_LEAN_OR_OVERLAY',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'branches': branches, 'basis_provider_status': records[basis['module']]['qualification'],
    'selected_basis_provider': records[basis['module']],
    'anchor_sources': [observe(ROOT / p) for p in anchors],
    'parents': [observe(p) for p in parents],
    'planning_driver': observe(__file__),
    'observations': [{'path': p, 'sha256': h} for p, h in sorted(observations.items())],
    'scope': 'Read-only current source/header/provider/provenance reauthentication. No Lean, dependency refresh, overlay, source or Git mutation. Historical companion/source-trace qualifications in parent inventories are retained; no whole-closure fresh replay claim.'}
require(not OUT.exists(), 'refuse to overwrite frozen inventory')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'counts': {k: v['counts'] for k, v in branches.items()},
                  'observations': len(observations)}, indent=2))
