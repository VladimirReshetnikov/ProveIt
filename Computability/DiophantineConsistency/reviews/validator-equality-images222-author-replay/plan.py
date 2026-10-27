"""Read-only authentication of the proposed equality-images leaf.
No Lean, overlay, dependency build or existing-source mutation is performed.
The broad NativeTheory alternative is inventoried by source only, not selected.
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
OUT = D / 'research/validator-equality-images222-plan.json'
OBS = []


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def pin(p, h=None, role='input'):
    v = sha(p)
    if h is not None and h != v:
        raise RuntimeError(f'changed {p}: {v} != {h}')
    r = {'path': str(p), 'sha256': v, 'role': role}
    OBS.append(r)
    return r


def strip_comments(text):
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
        raise RuntimeError('unclosed block comment')
    return ''.join(out)


def imports(p):
    text = strip_comments(pathlib.Path(p).read_text())
    out = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for l in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        out.extend(re.findall(r'[\w.]+', l))
    return list(dict.fromkeys(out))


bp = REV / 'validator-source-derivation222-replay.json'
basepin = pin(bp, 'd688e71398add24dc4e54cdb2ba002d45524c3fbe2af324bc2d95f411f4e195c', 'frozen author provenance')
base = json.loads(bp.read_text())
pp = REV / 'validator-source-derivation222-peer-replay.json'
peerpin = pin(pp, role='independent successful replay')
peer = json.loads(pp.read_text())
assert peer['status'] == 'PASS'
parents = [basepin, peerpin, pin(REV / 'validator-source-derivation222-peer.md',
    '3f69dbd65832aea4e6b7e4926b8040b0b49763f97b7b8610d31e2ec7a02402d3', 'independent mathematical review')]
pin(peer['manifest']['path'], peer['manifest']['sha256'], 'independent manifest')
mods = {m['module']: copy.deepcopy(m) for m in base['inputs']['modules']}
external = {e['module']: copy.deepcopy(e) for e in base['inputs']['external']}
leaf = peer['records'][0]
assert leaf['module'] == 'ZFCinPA.ValidatorSourceDerivation222'
assert leaf['exit_code'] == 0 and leaf['matches_author']
mods[leaf['module']] = {
    'module': leaf['module'], 'source': leaf['source']['path'],
    'source_sha256': leaf['source']['sha256'], 'objects': [leaf['object']],
    'imports': imports(leaf['source']['path']), 'provenance': peerpin,
    'action': 'proposed reuse of independent current-source replay, author-byte identical',
}
seen, boundaries, order = set(), set(), []


def visit(n):
    if n in seen:
        return
    if n not in mods:
        if n not in external:
            raise RuntimeError('unknown boundary ' + n)
        boundaries.add(n)
        return
    seen.add(n)
    m = mods[n]
    h = imports(m['source'])
    assert h == list(dict.fromkeys(m['imports'])), n
    for dep in h:
        visit(dep)
    order.append(n)


visit(leaf['module'])
for n in order:
    m = mods[n]
    pin(m['source'], m['source_sha256'], 'selected current source')
    for o in m['objects']:
        pin(o['path'], o['sha256'], 'selected cached artifact')
    if isinstance(m.get('trace'), dict):
        tr = m['trace']
        pin(tr['trace'], tr['trace_sha256'], 'retained accepted Lean4.32 trace')
for n in sorted(boundaries):
    e = external[n]
    pin(e['path'], e['sha256'], 'explicit selected boundary')
for k in ['compiler', 'manifest', 'toolchain']:
    pin(base['inputs'][k], base['inputs'][k + '_sha256'], k)
counts = {'cached_modules': len(order),
          'foundation_modules': sum(n.startswith('Foundation.') for n in order),
          'object_artifacts': sum(len(mods[n]['objects']) for n in order),
          'external_boundaries_including_Init': len(boundaries)}
assert tuple(counts.values()) == (165, 117, 516, 40)
assert not any(n.startswith('ZFCinPA.R2') for n in order)

# The alternative is source-only: do not treat old cache candidates as selected
# objects or authorize any compile. Re-read every traversed import header.
oldpath = REV / 'fixed-consistency-nat-cache-audit/closure.json'
oldpin = pin(oldpath, role='source-location guide for unselected broad alternative')
source_map = {m['module']: m['source'] for m in json.loads(oldpath.read_text())['modules']}
source_map.update({n: m['source'] for n, m in mods.items()})
alternatives = []
for target in ['ZFCinPA.ZFDelta1', 'ZFCinPA.NativeTheory']:
    alt, ext, altorder = set(), set(), []
    def av(n):
        if n in alt:
            return
        if n not in source_map:
            ext.add(n)
            return
        alt.add(n)
        for dep in imports(source_map[n]):
            av(dep)
        altorder.append(n)
    av(leaf['module'])
    av(target)
    added = [n for n in altorder if n not in seen]
    alternatives.append({'target': target, 'selected': False,
        'union_modules': len(alt), 'union_foundation': sum(n.startswith('Foundation.') for n in alt),
        'boundary_names_count': len(ext), 'boundary_names': sorted(ext),
        'added_sources': [{'module': n, **pin(source_map[n], role='unselected alternative source/header only')} for n in added],
        'object_authentication': 'not performed or claimed for this unselected alternative'})

anchors = []
for n in ['R2Ax', 'R2Fixed', 'R2Native', 'ConstructibleInterpretation', 'ZFDelta1',
          'NativeTheory', 'Translation', 'ValidatorAtomicTransport222',
          'ValidatorSeedWitness222', 'ValidatorEind222', 'ValidatorFormulaEncoder222']:
    anchors.append(pin(ROOT / f'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/{n}.lean', role='mathematical source anchor, no extra import'))
pin(__file__, role='fully read read-only audit script')
for r in OBS:
    assert sha(r['path']) == r['sha256'], r['path']
result = {'status': 'READ_ONLY_AUTHENTICATED_PLAN_NO_LEAN_EXECUTION',
    'snapshot': subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(),
    'proposed_imports': [leaf['module']], 'counts': counts, 'parents': parents,
    'modules': [mods[n] for n in order], 'external': [external[n] for n in sorted(boundaries)],
    'selected_new_provider': leaf, 'unselected_source_only_alternatives': alternatives,
    'alternative_source_guide': oldpin, 'mathematical_anchors': anchors,
    'executed_lean_processes': 0, 'created_overlays': 0, 'observations': OBS,
    'scope': 'Only accepted/frozen cached pairs rehashed; independent Derivation replay selected, root acceptance separately pending. No dependency/Foundation build; unselected wide alternatives are source-only cost estimates.'}
assert not OUT.exists(), str(OUT)
OUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'path': str(OUT), 'sha256': sha(OUT), 'counts': counts,
    'observations': len(OBS), 'alternatives': [(a['target'], a['union_modules'], a['union_foundation'], a['boundary_names_count']) for a in alternatives]}, indent=2))
