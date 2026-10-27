#!/usr/bin/env python3
"""Authenticate the proposed C222 derivation imports without executing Lean.

Only the new planning JSON is written. No overlay, package build, or source
mutation occurs. Existing accepted author and independent records stay intact.
"""
import copy
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
OUT = D / 'research/validator-source-derivation222-plan.json'
OBS = []


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def pin(path, expected=None, role='input'):
    actual = sha(path)
    if expected is not None and actual != expected:
        raise RuntimeError(f'changed {path}: {actual} != {expected}')
    record = {'path': str(path), 'sha256': actual, 'role': role}
    OBS.append(record)
    return record


def read(name, expected=None):
    path = REV / name
    record = pin(path, expected, 'accepted provenance record')
    return json.loads(path.read_text()), record


def strip_comments(text):
    # Preserve newlines; nested Lean block comments and line comments are both
    # ignored before reading the import header. These sources have no imports
    # inside multiline strings before the first declaration.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j == -1 else j
            out.extend(' ' * (j - i))
            i = j
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('unclosed Lean block comment')
    return ''.join(out)


def imports(path):
    text = strip_comments(pathlib.Path(path).read_text())
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))


base, base_pin = read('validator-source-quantifier-context222-replay.json',
                     '1898017ecd78b4de060a0f0c466e8c75a77c7a4bfe37a12ffec4850961051d38')
neg, neg_pin = read('validator-source-negation222-peer-replay.json',
                   'f9013d100f8e3365c7fe19e39857ad9bba3fa5f3ef084c2a576d8745159294ef')
quant, quant_pin = read('validator-source-quantifier-context222-root-replay/state.json',
                       'be351f9e011a5fc3ccedd5fd63a43b7c0094d8fe9b7cf57409da703d493a397d')
assert quant['status'] == 'PASS'
modules = {m['module']: copy.deepcopy(m) for m in base['inputs']['modules']}
external = {e['module']: copy.deepcopy(e) for e in base['inputs']['external']}
parents = [base_pin, neg_pin, quant_pin]
for name in [
    'validator-source-negation222-peer.md',
    'validator-source-negation222-root.md',
    'validator-source-negation222-root-authentication/validator-source-negation222-root-authentication.json',
    'validator-source-quantifier-context222-root.md',
    'validator-source-quantifier-context222-root-replay/FILES.json',
]:
    parents.append(pin(REV / name, role='accepted independent/root provenance'))
selected = []
for leaves, provenance in [(neg['commands'], neg_pin), (quant['completed'], quant_pin)]:
    for leaf in leaves:
        if leaf['module'].endswith('Checks'):
            continue
        assert leaf['exit_code'] == 0
        assert leaf['object']['sha256'] == leaf['expected_object']
        modules[leaf['module']] = {
            'module': leaf['module'], 'source': leaf['source'],
            'source_sha256': leaf['source_sha256'], 'objects': [leaf['object']],
            'provenance': provenance,
            'action': 'reuse accepted independently replayed leaf, author-byte identical',
        }
        selected.append(leaf['module'])

seen, boundaries, order = set(), set(), []


def visit(name):
    if name in seen:
        return
    if name not in modules:
        if name not in external:
            raise RuntimeError(f'unrecorded boundary {name}')
        boundaries.add(name)
        return
    seen.add(name)
    m = modules[name]
    actual = imports(m['source'])
    if 'imports' in m and list(dict.fromkeys(m['imports'])) != actual:
        raise RuntimeError(f'header mismatch {name}')
    if 'imports' in m and m['imports'] != actual:
        m['inherited_import_occurrences'] = m['imports']
    m['imports'] = actual
    for dep in actual:
        visit(dep)
    order.append(name)


targets = ['ZFCinPA.ValidatorSourceNegation222',
           'ZFCinPA.ValidatorSourceQuantifierContext222']
for target in targets:
    visit(target)
for name in order:
    m = modules[name]
    pin(m['source'], m['source_sha256'], 'current prerequisite source')
    for obj in m['objects']:
        pin(obj['path'], obj['sha256'], 'accepted cached object/companion')
    if isinstance(m.get('trace'), dict):
        tr = m['trace']
        pin(tr['trace'], tr['trace_sha256'], 'previously authenticated Lean4.32 Lake trace')
for name in sorted(boundaries):
    e = external[name]
    pin(e['path'], e['sha256'], 'explicit package/toolchain boundary')
for key, hkey in [('compiler', 'compiler_sha256'), ('manifest', 'manifest_sha256'),
                  ('toolchain', 'toolchain_sha256')]:
    pin(base['inputs'][key], base['inputs'][hkey], key)
guide = pin(ROOT / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Main.lean',
            role='historical source-only guide, not imported')
anchors = []
for name in ['ValidatorSourceNegation222', 'ValidatorSourceQuantifierContext222',
             'ValidatorProofContext222', 'ValidatorRelationalCore222',
             'ValidatorEnvironmentAlpha222', 'ValidatorEnvironmentStreams222',
             'ValidatorFormulaEncoder222', 'ValidatorProvability222']:
    anchors.append(pin(ROOT / f'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/{name}.lean',
                       role='mathematical source anchor'))
script_pin = pin(__file__, role='fully read read-only inventory script')
counts = {
    'cached_modules': len(order),
    'foundation_modules': sum(n.startswith('Foundation.') for n in order),
    'object_artifacts': sum(len(modules[n]['objects']) for n in order),
    'external_boundaries_including_Init': len(boundaries),
    'executed_lean_processes': 0, 'created_overlays': 0,
    'proposed_fresh_leaves': 2,
}
assert counts['cached_modules'] == 164
assert counts['foundation_modules'] == 117
assert counts['object_artifacts'] == 515
assert counts['external_boundaries_including_Init'] == 40
assert modules['Foundation.FirstOrder.Basic.AesopInit']['imports'] == [
    'Init', 'Aesop', 'Aesop.Frontend.Command']
assert not any(n.startswith('ZFCinPA.R2') for n in order)
basic = 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic'
assert basic in seen
for p in OBS:
    if sha(p['path']) != p['sha256']:
        raise RuntimeError(f'changed during authentication: {p["path"]}')
result = {
    'status': 'READ_ONLY_PLAN_AUTHENTICATED_NO_LEAN_EXECUTION',
    'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'proposed_imports': targets, 'counts': counts, 'parents': parents,
    'delta_from_accepted_quantifier_cache': sorted(seen - {m['module'] for m in base['inputs']['modules']}),
    'selected_independent_leaf_modules': selected,
    'modules': [modules[n] for n in order],
    'external': [external[n] for n in sorted(boundaries)],
    'already_cached_proof_basic': modules[basic],
    'source_only_guide': guide, 'mathematical_anchors': anchors,
    'script': script_pin,
    'scope': 'All reused inputs rehashed; no dependency/Foundation build, no old R2 import, no Lean invocation or created overlay. Previously authenticated Lake trace provenance retained, not regenerated.',
    'observations': OBS,
}
if OUT.exists():
    raise RuntimeError(f'refusing to overwrite frozen plan {OUT}')
OUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'counts': counts,
                  'observations': len(OBS)}, ensure_ascii=False))
