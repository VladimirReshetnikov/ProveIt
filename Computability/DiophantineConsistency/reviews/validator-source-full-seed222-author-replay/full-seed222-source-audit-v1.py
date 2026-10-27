#!/usr/bin/env python3
"""Read-only cache/source audit; writes only the new proposal JSON."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'research/validator-source-full-seed222-plan.json'
PLAN = D / 'research/validator-source-full-seed222-plan.md'
observations = []

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def pin(p, expected=None, role='read-only observation'):
    p = Path(p)
    h = sha(p)
    if expected is not None and h != expected:
        raise RuntimeError(f'PIN MISMATCH: {p}: expected {expected}, found {h}')
    r = {'path': str(p), 'sha256': h, 'bytes': p.stat().st_size, 'role': role}
    observations.append(r)
    return r

def load(p):
    pin(p, role='accepted provider metadata')
    return json.loads(Path(p).read_text())

def imports(p):
    text = Path(p).read_text()
    # Nested block comments and line comments, preserving newlines.
    clean = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                clean.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            clean.append(text[i])
            i += 1
    assert depth == 0
    found = ['Init']
    for line in ''.join(clean).splitlines():
        m = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$', line)
        if m:
            for name in m.group(1).split():
                assert re.fullmatch(r'[\w.]+', name), (p, name)
                if name not in found:
                    found.append(name)
    return found

eq = load(REV / 'validator-equality-images222-cache.json')
seed_author = load(REV / 'validator-seed-padding222-replay.json')
pin(seed_author['inputs']['path'], seed_author['inputs']['sha256'])
seed_inputs = json.loads(Path(seed_author['inputs']['path']).read_text())
seed_peer_path = REV / 'validator-seed-padding222-peer-replay.json'
seed_peer = load(seed_peer_path)
pin(REV / 'validator-seed-padding222-root.md', role='root acceptance')

records = {r['module']: r for r in seed_inputs['modules']}
records.update({r['module']: r for r in eq['modules']})
fresh = seed_peer['records'][0]
assert fresh['module'] == 'ZFCinPA.ValidatorSeedPadding222'
assert fresh['exit_code'] == 0 and fresh['matches_author']
records[fresh['module']] = {
    'module': fresh['module'],
    'source': fresh['source']['path'],
    'source_sha256': fresh['source']['sha256'],
    'objects': [fresh['object']],
    'imports': imports(fresh['source']['path']),
    'provenance': {'path': str(seed_peer_path), 'sha256': sha(seed_peer_path),
                   'role': 'accepted independent current-source replay'},
}
roots = ['ZFCinPA.ValidatorSeedPadding222',
         'ZFCinPA.ValidatorSourceNegation222',
         'ZFCinPA.ValidatorExistentialRules222']
seen, outside, ordered = set(), set(), []

def visit(n):
    if n in seen:
        return
    if n not in records:
        outside.add(n)
        return
    seen.add(n)
    rec = records[n]
    actual = imports(rec['source'])
    assert set(actual) == set(rec['imports']), (n, actual, rec['imports'])
    for child in actual:
        visit(child)
    ordered.append(rec)

for n in roots:
    visit(n)

external_all = {r['module']: r for r in seed_inputs['external']}
external_all.update({r['module']: r for r in eq['external']})
external = [external_all[n] for n in sorted(outside)]
for rec in ordered:
    pin(rec['source'], rec['source_sha256'], 'current cached prerequisite source')
    for obj in rec['objects']:
        pin(obj['path'], obj['sha256'], 'accepted cached object/companion')
    if 'provenance' in rec:
        pv = rec['provenance']
        pin(pv['path'], pv['sha256'], 'selected provider record')
for rec in external:
    pin(rec['path'], rec['sha256'], 'explicit external primary boundary')
for key in ['compiler', 'manifest', 'toolchain']:
    pin(eq[key], eq[key + '_sha256'], 'compiler/configuration boundary')

bb = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
zf = ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'
full_bb = ['KSeedInterface222', 'KSeed222', 'KSeedDirect222', 'KLowerSeed',
           'KLowerRaw', 'KLowerRel', 'KLowerTag', 'KLowerEqv', 'KLowerQHyp',
           'ArithmeticSeedTemplates222']
full_zf = ['ValidatorSeedWitness222', 'ValidatorSeedClosure222', 'ValidatorSeedImage222',
           'ValidatorSeedPadding222', 'ValidatorNativeGic254', 'NativeGicDelta1',
           'NativeTheory', 'R2Ax', 'ValidatorEnvironmentSubstitution222',
           'ValidatorEnvironmentAlpha222', 'ValidatorEnvironmentStreams222',
           'ValidatorEindContext222', 'ValidatorExistentialRules222',
           'ValidatorQuantifierRules222', 'ValidatorSourceNegation222',
           'ValidatorSourceDerivation222', 'ValidatorEqualityImages222']
read_sources = []
for base, names in [(bb, full_bb), (zf, full_zf)]:
    for name in names:
        rec = pin(base / f'{name}.lean', role='source inspected for mathematical audit')
        rec['inspection'] = 'complete source (this audit or immediately preceding accepted work)'
        read_sources.append(rec)
for base, name, ranges in [
    (bb, 'KEind222', '1-160: literal Eind/th and completeness boundary'),
    (bb, 'ProfileCollection', '75-135: App/Bisim/Eqv and elementary properties'),
    (bb, 'ProfileComposition', '250-275: Member and quotient-extensionality boundary'),
    (zf, 'R2Fixed', '235-430: old container circuit/source bridge'),
]:
    rec = pin(base / f'{name}.lean', role='source excerpt inspected for mathematical audit')
    rec['inspection'] = ranges
    read_sources.append(rec)

counts = {'cached_modules': len(ordered),
          'foundation_modules': sum(r['module'].startswith('Foundation.') for r in ordered),
          'object_artifacts': sum(len(r['objects']) for r in ordered),
          'external_boundaries_including_Init': len(external)}
assert list(counts.values()) == [166, 117, 517, 40], counts
plan_pin = pin(PLAN, role='frozen read-only mathematical proposal')
driver_pin = pin(__file__, role='read-only metadata auditor; no compiler invocation')
snapshot = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
result = {
    'status': 'READ_ONLY_PROPOSAL_AND_CACHE_LEAD',
    'scope': 'No Lean execution, overlay construction, source theorem edits, shared-object writes, or Git mutation.',
    'snapshot': snapshot,
    'plan': plan_pin, 'driver': driver_pin,
    'proposed_direct_imports': roots,
    'counts': counts, 'modules_dependency_order': ordered, 'external': external,
    'inspected_sources': read_sources,
    'observations': observations,
    'fresh_compile_count': 0,
    'proposed_fresh_leaf_count_after_approval': 2,
    'excluded': ['NativeTheory/NativeGicDelta1/R2 proof imports',
                 'schema recognizer and arbitrary universal-closure membership',
                 'raw CP/GIC AxOK', 'tagged/quotient source interpretation',
                 'closed ZF/source/machine/HA equation equivalence'],
    'provenance_limit': 'Rehashed selected accepted records and current source/object bytes. A new build must also reauthenticate its final full parent/companion provenance and pre/post pins.',
}
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'plan_sha256': sha(PLAN),
                  'counts': counts, 'observations': len(observations)}, indent=2))
