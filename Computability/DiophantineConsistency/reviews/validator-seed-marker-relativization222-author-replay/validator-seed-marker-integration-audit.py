"""Read-only marker integration inventory. No Lean, overlay, or cache mutation."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV, RESEARCH = D / 'reviews', D / 'research'
OUT = RESEARCH / 'validator-seed-marker-integration-plan.json'
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
    require(path not in observations or observations[path] == actual, 'mid-audit drift: ' + path)
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
    require(depth == 0, 'unclosed comment')
    source = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', source, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', source, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))


def manifest(path, expected):
    observe(path, expected)
    data = read(path)
    for item in data['files'] if isinstance(data, dict) else data:
        p = Path(item['path'])
        base = ROOT if p.parts[0] in ['Logic', 'Computability'] else path.parent
        observe(base / p, item['sha256'])


marker_plan_path = RESEARCH / 'validator-seed-marker-discharge-cache-plan.json'
marker_peer_path = REV / 'validator-seed-marker-discharge222-peer-replay.json'
collection_plan_path = RESEARCH / 'validator-seed-tagged-collection-cache-plan.json'
collection_author_path = REV / 'validator-seed-tagged-collection222-replay.json'
observe(marker_plan_path, '47a392b42dfadc0dd778049415bec00530e08c410176f21ee88542be11733354')
observe(marker_peer_path, 'e7ffbe74bbe436242fa2ceb303f70a620322ec9fea91baa1d51ce0ce0b590298')
observe(collection_plan_path, '94c923959cc8870c08f452e26d330c68b8bea7f43961595498e5eb355cdde911')
observe(collection_author_path, '0c06fbabf38086b3948a51d9af1396bceb5861e18d80dc240bc0a2d244d39aa4')
mp, peer = read(marker_plan_path), read(marker_peer_path)
cp, ca = read(collection_plan_path), read(collection_author_path)
require(peer['status'] == 'PASS' and ca['status'] == 'PASS', 'parent terminal state')
for item in mp['observations'] + cp['observations']:
    observe(item['path'], item['sha256'])
manifest(REV / 'validator-seed-marker-discharge222-peer-replay/FILES.json',
         '54a4ee9868b03f8ab018ea5e18daea9587e8f16429287689e6e580b768a6e4af')
manifest(Path(peer['author_manifest']['path']), peer['author_manifest']['sha256'])
manifest(Path(ca['bundle']) / 'FILES.json', ca['manifest_sha256'])
for key in ['author_packet', 'author_receipt', 'inputs', 'state', 'durable_state']:
    observe(peer[key]['path'], peer[key]['sha256'])
observe(REV / 'validator-seed-marker-discharge222-peer.md')
observe(REV / 'validator-seed-tagged-collection222-author.md',
        '0ae0f2c24b9bc54f3e2e29e10f37f22a073b62dd4d522dae9bee259624136421')

records = {r['module']: r for r in mp['modules']}
for r in cp['modules_dependency_order']:
    if r['module'] in records:
        old = records[r['module']]
        require(old['source_sha256'] == r['source_sha256'], 'shared source disagreement')
        require([p['sha256'] for p in old['objects']] ==
                [p['sha256'] for p in r['objects']], 'shared object disagreement')
    else:
        records[r['module']] = r

marker = peer['records'][0]
collection = ca['completed'][0]
require(marker['module'] == 'ZFCinPA.ValidatorSeedMarkerDischarge222', 'wrong Marker record')
require(collection['module'] == 'ZFCinPA.ValidatorSeedTaggedCollection222', 'wrong Collection record')
records[marker['module']] = {
    'module': marker['module'], 'source': marker['source']['path'],
    'source_sha256': marker['source']['sha256'], 'objects': [marker['object']],
    'imports': imports(marker['source']['path']), 'provenance_parent': str(marker_peer_path),
    'qualification': 'Independent peer accepted by ROOT; selected directly, author evidence retained.'}
records[collection['module']] = {
    'module': collection['module'], 'source': collection['source'],
    'source_sha256': collection['source_sha256'], 'objects': [collection['object']],
    'imports': imports(collection['source']), 'provenance_parent': str(collection_author_path),
    'qualification': 'Candidate author PASS only; independent ROOT acceptance pending at plan freeze.'}
externals = {r['module']: r for r in mp['external']}
for r in cp['external']:
    require(r['module'] not in externals or externals[r['module']]['sha256'] == r['sha256'],
            'external disagreement')
    externals[r['module']] = r


def branch(targets, search_paths, expected):
    order, seen, visiting, boundary_names = [], set(), set(), set()

    def visit(name):
        if name in seen:
            return
        require(name not in visiting, 'import cycle: ' + name)
        if name not in records:
            require(name in externals, 'unrecorded external: ' + name)
            boundary_names.add(name)
            return
        visiting.add(name)
        r = records[name]
        observe(r['source'], r['source_sha256'])
        actual = imports(r['source'])
        require(set(actual) == set(r.get('actual_imports', r['imports'])), 'header drift: ' + name)
        for dependency in actual:
            visit(dependency)
        for obj in r['objects']:
            observe(obj['path'], obj['sha256'])
        for key in ['provenance', 'trace', 'lake_trace']:
            item = r.get(key)
            if isinstance(item, dict) and 'path' in item and 'sha256' in item:
                observe(item['path'], item['sha256'])
        for absent in r.get('absent_companions', []):
            require(not Path(absent).exists(), 'historically absent companion appeared: ' + absent)
        visiting.remove(name)
        seen.add(name)
        order.append({**r, 'actual_imports': actual})

    for name in targets:
        visit(name)
    boundaries = [externals[n] for n in sorted(boundary_names)]
    providers = []
    for r in order + boundaries:
        name = r['module']
        for item in r['objects'] if 'objects' in r else [r]:
            stem = name.split('.')[-1]
            filename = Path(item['path']).name
            require(filename.startswith(stem + '.'), 'artifact name mismatch')
            relative = name.replace('.', '/') + filename[len(stem):]
            found = next((Path(p) / relative for p in search_paths if (Path(p) / relative).is_file()), None)
            require(found is not None, 'missing actual first provider: ' + relative)
            providers.append({'module': name, 'relative': relative,
                              **observe(found, item['sha256'])})
    counts = {'cached_modules': len(order),
              'foundation': sum(r['module'].startswith('Foundation.') for r in order),
              'artifacts': sum(len(r['objects']) for r in order),
              'external_boundaries': len(boundaries), 'artifact_providers': len(providers)}
    require(counts == expected, 'unexpected closure: ' + str(counts))
    return {'imports': targets, 'counts': counts, 'modules_dependency_order': order,
            'external': boundaries, 'existing_search_path': search_paths,
            'actual_first_artifact_providers': providers, 'new_prerequisite_refresh': []}


packages = mp['package_paths']
minimal = branch([marker['module']], [peer['provider']] + packages,
                 {'cached_modules': 203, 'foundation': 136, 'artifacts': 611,
                  'external_boundaries': 45, 'artifact_providers': 656})
collection_provider = str(Path(collection['object']['path']).parents[1])
integration_paths = list(dict.fromkeys([collection_provider, peer['provider']] +
                                      cp['existing_search_path'] + packages))
integration = branch([marker['module'], collection['module']], integration_paths,
                     {'cached_modules': 210, 'foundation': 136, 'artifacts': 618,
                      'external_boundaries': 45, 'artifact_providers': 663})

zfc = ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'
busy = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
foundation = Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation')
anchors = [zfc / (n + '.lean') for n in [
    'InternalInterpretation', 'ModelCodedProofRenaming', 'SetRelativization',
    'ValidatorSeedMarkerDischarge222', 'ValidatorSeedMarkerDischarge222Checks',
    'ValidatorSeedTaggedCollection222', 'ValidatorSeedTaggedCollection222Checks',
    'ValidatorSeedSourceBasis222', 'ValidatorFullSeedTheory222',
    'ValidatorSourceDerivation222', 'NativeGicDelta1', 'NativeTheory', 'NativeSchema', 'LSchema']]
anchors += [busy / (n + '.lean') for n in ['KLowerTag', 'KLowerEqv', 'KLowerQHyp', 'KQHyp', 'KQ1ZF']]
anchors += [foundation / 'FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean',
            foundation / 'FirstOrder/Bootstrapping/Syntax/Term/Basic.lean',
            ROOT / 'Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalRelativization.lean',
            RESEARCH / 'validator-seed-marker-counter-proposal.md',
            RESEARCH / 'validator-seed-tagged-interpretation-plan.md',
            RESEARCH / 'validator-seed-tagged-interpretation-plan.json']
anchor_records = [observe(p) for p in anchors]
result = {
    'status': 'READ_ONLY_PROPOSAL_NO_LEAN_NO_OVERLAY_NO_REFRESH',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'branches': {'recommended_raw_marker_transport': minimal,
                 'later_collection_binding_candidate_only': integration},
    'selected_marker_provider': records[marker['module']],
    'candidate_collection_provider': records[collection['module']],
    'compiler': observe(mp['compiler']['path'], mp['compiler']['sha256']),
    'toolchain': observe(mp['toolchain']['path'], mp['toolchain']['sha256']),
    'manifest': observe(mp['manifest']['path'], mp['manifest']['sha256']),
    'parents': [observe(p) for p in [marker_plan_path, marker_peer_path,
                                   collection_plan_path, collection_author_path]],
    'anchor_sources': anchor_records, 'driver': observe(__file__),
    'observations': [{'path': p, 'sha256': h} for p, h in sorted(observations.items())],
    'qualification': 'No new proof or compiler claim. Marker selects the newly accepted peer; '
                     'Collection remains author-only pending independent acceptance. Reused historical '
                     'InternalRelativization retains its original source/run and missing-companion '
                     'qualification. Read-only hashing does not make that prerequisite freshly compiled.'}
require(not OUT.exists(), 'refuse to overwrite inventory')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'output': str(OUT), 'sha256': sha(OUT),
                  'branches': {k: v['counts'] for k, v in result['branches'].items()},
                  'observations': len(observations)}, indent=2))
