"""Read-only cache and source authentication for a proposed new source leaf.

No compiler, import of project Python, object copy, or source mutation.
The sole output is the adjacent JSON planning receipt.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'

def pin(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}

def verify(record):
    observed = pin(record['path'])
    if observed['sha256'] != record['sha256']:
        raise RuntimeError(('changed input', record['path'], observed['sha256']))
    return observed

parent_path = Path('/tmp/native-adaptive-mersenne-8cbwhqb1/inputs.json')
root_path = DC / 'reviews/native-adaptive-mersenne-root-replay/ROOT.json'
parent = json.loads(parent_path.read_text())
root = json.loads(root_path.read_text())
assert root['status'] == 'PASS'
selected = list(parent['selected_custom'])
fresh = root['records'][0]
assert fresh['module'] == 'DiophantineConsistency.NativeAdaptiveMersenne'
assert fresh['exit_code'] == 0 and fresh['matches_author']
selected.append({'module': fresh['module'], 'source': fresh['source'],
                 'object': fresh['object'],
                 'actual_imports': ['Init', 'DiophantineConsistency.NativeAdaptivePowerRecovery']})
observed = [verify(r[key]) for r in selected for key in ('source', 'object')]
external = parent['external_boundary']
for row in external:
    observed.append(verify(row['source']))
    observed.extend(verify(r) for r in row['artifacts'])
names = {r['module'] for r in selected}
boundary = {r['module'] for r in external}
assert len(names) == len(selected) == 33
assert all(set(r['actual_imports']) <= names | boundary for r in selected)

ordinary_path = Path('/tmp/native-ordinary-source-root-7cz0jxs2/ROOT.json')
ordinary = json.loads(ordinary_path.read_text())
ordinary_names = {r['module'] for r in ordinary['selected_custom']}
ordinary_names.add('DiophantineConsistency.NativeOrdinarySourceConstruction')
sources = [
    'Lean/DiophantineConsistency/NativeAdaptiveUnitFactors.lean',
    'Lean/DiophantineConsistency/NativeOrdinarySourceConstruction.lean',
    'Lean/DiophantineConsistency/NativeShiftedSourceAdapter.lean',
    'Lean/DiophantineConsistency/Carrier66Source.lean',
    'Lean/DiophantineConsistency/NativePellFirstIndex.lean',
    'Lean/DiophantineConsistency/NativePositiveSourceConstruction.lean',
    'Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean',
    'candidates/free-j-polarized-positive/source/positive/p13_free_J.json',
    'candidates/free-j-polarized-positive/source/positive/PROOF.md',
]
result = {
    'status': 'READ_ONLY_PLAN_AUTHENTICATED',
    'scope': 'Only the proposed sole-Mersenne-import source-restoration leaf is authenticated here. No compiler was invoked. Later graph/native endpoints are not built or newly authenticated.',
    'provider': pin(root_path), 'parent_inputs': pin(parent_path),
    'selected_custom': selected, 'external_boundary': external,
    'observations': observed, 'counts': {'custom': len(selected),
        'external': len(external),
        'external_companions': sum(len(r['artifacts']) for r in external),
        'observations': len(observed)},
    'later_dependency_inventory_only': {
        'ordinary_provider': pin(ordinary_path),
        'ordinary_with_main': len(ordinary_names),
        'union_before_new_leaves_or_unit_factors': len(names | ordinary_names),
        'adaptive_additions': sorted(names - ordinary_names),
        'warning': 'This is a module-name union, not a new authentication of the broad native provider.'},
    'additional_source_only_pins': [pin(DC / s) for s in sources],
    'audit_script': pin(__file__),
}
(DC / 'research/adaptive-source-restoration2011-cache-audit.json').write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps(result['counts'], sort_keys=True))
