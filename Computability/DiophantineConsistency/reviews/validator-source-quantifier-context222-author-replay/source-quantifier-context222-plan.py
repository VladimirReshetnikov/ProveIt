#!/usr/bin/env python3
"""Read-only input authentication for the proposed quantifier-context leaf.

Writes one NEW planning inventory; never executes Lean or constructs an overlay.
"""
import copy
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT / 'Computability/DiophantineConsistency/reviews'
OUT = ROOT / 'Computability/DiophantineConsistency/research/validator-source-quantifier-context222-plan.json'
OBS = []


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def pin(path, expected=None, role='input'):
    value = sha(path)
    if expected is not None and value != expected:
        raise RuntimeError(f'changed {path}: {value} != {expected}')
    result = {'path': str(path), 'sha256': value, 'role': role}
    OBS.append(result)
    return result


def read(name):
    path = REV / name
    record = pin(path, role='accepted provenance record')
    return json.loads(path.read_text()), record


def imports(path):
    text = re.sub(r'/\-.*?\-/', '', pathlib.Path(path).read_text(), flags=re.S)
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(re.findall(r'[\w.]+', line.split('--', 1)[0]))
    return list(dict.fromkeys(result))


base, base_pin = read('validator-source-negation222-replay.json')
ex, ex_pin = read('validator-existential-rules222-replay.json')
modules = {m['module']: copy.deepcopy(m) for m in base['inputs']['modules']}
for m in ex['inputs']['modules']:
    if m['module'] in modules:
        assert m['source_sha256'] == modules[m['module']]['source_sha256']
    else:
        modules[m['module']] = copy.deepcopy(m)
external = {m['module']: copy.deepcopy(m) for m in base['inputs']['external']}
for e in ex['inputs']['external']:
    if e['module'] in external:
        assert e['sha256'] == external[e['module']]['sha256']
    else:
        external[e['module']] = copy.deepcopy(e)

parents = [base_pin, ex_pin]
selected_root = []
for name in [
    'validator-proof-context222', 'validator-existential-rules222',
    'validator-quantifier-rules222', 'validator-environment-streams222',
    'validator-environment-substitution222', 'validator-environment-vacuity222',
    'validator-environment-alpha222', 'validator-eind-context222',
    'validator-atomic-transport222',
]:
    record, record_pin = read(name + '-root-replay/ROOT.json')
    parents.append(record_pin)
    if 'state' in record:
        assert record['state']['status'] == 'PASS'
        leaves = record['state']['completed']
    else:
        assert record['status'] == 'PASS'
        leaves = record['records']
    for leaf in leaves:
        if leaf['module'].endswith('Checks'):
            continue
        assert leaf['exit_code'] == 0 and leaf['matches_author']
        source = leaf['source']
        if not isinstance(source, dict):
            source = {'path': source, 'sha256': leaf['source_sha256']}
        obj = leaf['object']
        if not isinstance(obj, dict):
            obj = {'path': obj, 'sha256': leaf['object_sha256']}
        modules[leaf['module']] = {
            'module': leaf['module'], 'source': source['path'],
            'source_sha256': source['sha256'], 'objects': [obj],
            'provenance': record_pin,
            'action': 'proposed reuse of accepted root fresh leaf, exact author-byte match',
        }
        selected_root.append(leaf['module'])

seen, boundaries, order = set(), set(), []


def visit(name):
    if name in seen:
        return
    if name not in modules:
        if name not in external:
            raise RuntimeError(f'unrecorded boundary: {name}')
        boundaries.add(name)
        return
    seen.add(name)
    record = modules[name]
    actual_imports = imports(record['source'])
    if 'imports' in record and list(dict.fromkeys(record['imports'])) != actual_imports:
        raise RuntimeError(f'header mismatch: {name}')
    if 'imports' in record and record['imports'] != actual_imports:
        record['inherited_import_occurrences'] = record['imports']
    record['imports'] = actual_imports
    for dep in actual_imports:
        visit(dep)
    order.append(name)


targets = ['ZFCinPA.ValidatorProofContext222', 'ZFCinPA.ValidatorExistentialRules222']
for target in targets:
    visit(target)
for name in order:
    record = modules[name]
    pin(record['source'], record['source_sha256'], 'current source')
    for obj in record['objects']:
        pin(obj['path'], obj['sha256'], 'accepted cached object/companion')
for name in sorted(boundaries):
    e = external[name]
    pin(e['path'], e['sha256'], 'explicit package/toolchain boundary')
for key, hkey in [('compiler', 'compiler_sha256'), ('manifest', 'manifest_sha256'),
                  ('toolchain', 'toolchain_sha256')]:
    pin(base['inputs'][key], base['inputs'][hkey], key)

guide = pin(ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Quant.lean',
            role='source-only historical guide; not imported')
for name in ['ValidatorProofContext222', 'ValidatorQuantifierRules222',
             'ValidatorExistentialRules222', 'ValidatorEnvironmentVacuity222',
             'ValidatorEnvironmentStreams222', 'ValidatorRelationalCore222',
             'ValidatorEnvironmentSubstitution222', 'ValidatorEnvironmentSubstitution254']:
    pin(ROOT / f'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/{name}.lean',
        role='mathematical API source anchor')
pin(__file__, role='read-only inventory script')
pin('/tmp/source-quantifier-context222-plan-v1.py', role='preserved duplicate-import preflight draft')
pin('/tmp/source-quantifier-context222-plan-v1-failure.txt', role='preflight metadata correction, not a source/compiler failure')
pin('/tmp/source-quantifier-context222-plan-v2.py', role='preserved explicit-Init preflight draft')
pin('/tmp/source-quantifier-context222-plan-v2-failure.txt', role='explicit-Init metadata correction, not a source/compiler failure')
counts = {
    'cached_modules': len(order),
    'foundation_modules': sum(n.startswith('Foundation.') for n in order),
    'object_artifacts': sum(len(modules[n]['objects']) for n in order),
    'external_boundaries_including_Init': len(boundaries),
    'executed_lean_processes': 0,
    'created_overlays': 0,
    'proposed_fresh_leaves': 2,
}
assert counts['cached_modules'] == 162
assert counts['foundation_modules'] == 117
assert counts['object_artifacts'] == 513
assert counts['external_boundaries_including_Init'] == 40
assert 'Aesop' in boundaries
assert modules['Foundation.FirstOrder.Basic.AesopInit']['imports'] == [
    'Init', 'Aesop', 'Aesop.Frontend.Command']
assert not any(n.startswith('ZFCinPA.R2') for n in order)
for record in OBS:
    if sha(record['path']) != record['sha256']:
        raise RuntimeError(f'changed during read-only authentication: {record["path"]}')
result = {
    'status': 'READ_ONLY_PLAN_AUTHENTICATED_NO_LEAN_EXECUTION',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'proposed_imports': targets,
    'counts': counts,
    'parents': parents,
    'selected_root_leaf_modules': sorted(selected_root),
    'delta_from_152_module_encoder_closure': sorted(seen - {m['module'] for m in base['inputs']['modules']}),
    'modules': [modules[n] for n in order],
    'external': [external[n] for n in sorted(boundaries)],
    'source_only_guide': guide,
    'header_note': 'Includes public meta import Aesop, preserving the original Context author record unchanged.',
    'scope_note': 'Rehash of already accepted source/object pairs and explicit boundaries only; no complete package reproof or new Foundation build.',
    'observations': OBS,
}
if OUT.exists():
    raise RuntimeError(f'refusing to overwrite frozen planning file {OUT}')
OUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'counts': counts,
                  'observations': len(OBS)}, ensure_ascii=False))
