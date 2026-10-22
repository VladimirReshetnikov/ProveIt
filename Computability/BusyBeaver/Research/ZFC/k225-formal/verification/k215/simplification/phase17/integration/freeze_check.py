"""Freeze reviewed phase17 source, producer and provenance inputs without executing them."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
HERE = Path('/tmp/k215-phase17-integration')
CHECK = Path('/tmp/k215-phase17-check')
PREP = Path('/tmp/k215-phase17-plan')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
dump = lambda x: (json.dumps(x, indent=2) + '\n').encode()

assert not CHECK.exists()
CHECK.mkdir()
original = (PREP / 'build.py').read_bytes()
assert hashlib.sha256(original).hexdigest() == 'a132a3970477ac9ede4e83a315e4525a9172aabb23c09b77ccaa23d4936b44c4'
assert sha(PREP / 'plan.json') == '8de0e2788c8cb2eb2eb8ab7d75668d86f3af7539566e63127174514f665b8c76'
(CHECK / 'draft-build.py').write_bytes(original)
(CHECK / 'draft-plan.json').write_bytes((PREP / 'plan.json').read_bytes())
runner = original.decode()
old = "m=row['module'];directory=out/('audit-'+m);directory.mkdir(exist_ok=True);source=directory/(m+'.lean');source.write_bytes(Path(row['source']).read_bytes())"
new = "m=row['module'];directory=out/('audit-'+m);directory.mkdir();source=directory/(m+'.lean');source.write_bytes(Path(row['source']).read_bytes())"
assert runner.count(old) == 1
runner = runner.replace(old, new)
(CHECK / 'build.py').write_text(runner)
plan = json.loads((PREP / 'plan.json').read_bytes())
assert len(plan['modules']) == 213
roots = ['Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
         'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean']
project = 0
for row in plan['modules']:
    assert sha(row['source']) == row['source_sha256']
    if '.' in row['module']:
        found = [ROOT / r / (row['module'].replace('.', '/') + '.lean') for r in roots]
        found = [p for p in found if p.is_file()]
        assert len(found) == 1 and Path(row['source']) == found[0], row['module']
        project += 1
assert project == 199
assert len(plan['absent_inputs']) == 7
for path in plan['absent_inputs']:
    assert not Path(path).exists() and not Path(path).is_symlink()
producer_names = ['generate_source215_lean.py', 'generate_source217_lean.py',
                  'generate_source218_lean.py', 'generate_source219_lean.py',
                  'generate_source221_lean.py', 'generate_source225_lean.py',
                  'generate_l2axiomsdom.py', 'generate_l2k222.py']
producer_root = ROOT / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
pins = dict(plan['present_inputs'])
def pin(path):
    path = Path(path)
    value = sha(path)
    if str(path) in pins:
        assert pins[str(path)] == value
    pins[str(path)] = value

for name in producer_names:
    pin(producer_root / name)
# Retain the earlier producer boundaries without misbinding their old source bytes.
old_boundary = json.loads(Path('/tmp/k215-phase16-check/producer-boundary.json').read_bytes())
for path in old_boundary['present_inputs']:
    if path.startswith(str(producer_root)) and Path(path).is_file():
        pin(path)
for name in ['KSource215Program', 'KSource215Data', 'KSource217', 'KSource218',
             'KSource219', 'KSource221', 'KSource225']:
    pin(ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC' / (name + '.lean'))
for name in ['conflict-resolution.json', 'local-cleanup-adoption.json',
             'machine-source-review.json', 'source-metrics.json',
             'client-continuity-review.json', 'clients.json', 'freeze_check.py']:
    pin(HERE / name)
for path in ['/tmp/k215-phase17-model-review/review.json',
             '/tmp/k215-phase17-model-review/typed-client-review.json',
             '/tmp/k215-phase17-model-review/candidate-map.json',
             '/tmp/k215-phase17-program-review/review.json',
             '/tmp/k215-phase17-program-review/static-audit.json',
             '/tmp/k215-phase17-program-review/renderer-cleanup.json']:
    pin(path)
phase16 = producer_root / 'verification/k215/simplification/phase16'
for name in ['README.md', 'basis-reference.json', 'basis.py', 'config.json',
             'controls.py', 'execution.tar.gz', 'freeze.json', 'index.json',
             'packet.py', 'result.json', 'review.py', 'independent/review.json',
             'independent/saved.json']:
    pin(phase16 / 'lean' / name)
plan['present_inputs'] = dict(sorted(pins.items()))
plan['status'] = 'FROZEN_REVIEWED_COMBINED_PHASE17_SOURCES'
plan['base_commit'] = 'd3ff74a6fadba99e05576fe844f1f5ace9eab648'
plan['main_commit'] = '140d832128fd43873f16e385766cd3cee08df8a9'
plan['preparation_notes'] = [
    'All thirteen old typed client source files and exact profiles retained.',
    '199 canonical project sources, fourteen typed clients and two endpoint audits.',
    'All nine site batches forced fresh by dependency-source changes.',
    'Eight changed producers reviewed as source; no producer or supplied verifier executed.',
    'Variant217–225 full certificate stacks are outside the selected compilation claim.',
    'Audits refuse existing output directories to preserve earlier raw records.',
]
(CHECK / 'plan.json').write_bytes(dump(plan))
freeze = {'status': 'FROZEN_FOR_PREFLIGHT_AND_PEER_REVIEW',
          'files': {n: sha(CHECK / n) for n in ['build.py', 'plan.json', 'draft-build.py', 'draft-plan.json']},
          'project_sources': project, 'providers': 213, 'typed_clients': 14,
          'fresh_expected': 171, 'reused_expected': 42,
          'additional_inputs': len(pins), 'absences': 7,
          'root_runner_delta': 'Only audit mkdir(exist_ok=True) becomes mkdir(), refusing overwrite.',
          'proofs_executed': False, 'supplied_code_executed': False}
(CHECK / 'freeze.json').write_bytes(dump(freeze))
print(json.dumps(freeze))
