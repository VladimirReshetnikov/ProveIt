#!/usr/bin/env python3
"""Static, bounded evidence only. Run from repository root; no Lean invocation."""
import hashlib
import json
import re
from pathlib import Path

repo = Path.cwd()
base = repo / 'Computability/DiophantineConsistency'
draft = base / 'research/ordinary14-natural79-dvd-reflection-slim-draft/NaturalDvdReflectionSlim.lean'
fixed = base / 'research/ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src'
precedent = base / 'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean'
external = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic')
basic = external / 'IOpen/Basic.lean'
schemata = external / 'Schemata.lean'
sha = lambda data: hashlib.sha256(data).hexdigest()
orig = draft.read_bytes()
alternative = fixed.read_bytes()
insertion = b'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'
assert alternative == insertion + orig
s = precedent.read_text()
assert 'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n' in s
assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
assert 'public import Foundation.FirstOrder.Arithmetic.Schemata' in basic.read_text()
assert 'notation "𝗜𝚺₁" => ISigma 1' in schemata.read_text()

roots = [base / 'Lean', repo / 'Computability/BusyBeaver/Lean']
pattern = re.compile(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', re.M)
visited, leaves, missing, hashes = set(), set(), set(), {}
def walk(name):
    if name in visited:
        return
    visited.add(name)
    if not name.startswith(('DiophantineConsistency.', 'BusyBeaver.')):
        leaves.add(name)
        return
    rel = Path(*name.split('.')).with_suffix('.lean')
    path = next((r / rel for r in roots if (r / rel).is_file()), None)
    if path is None:
        missing.add(name)
        return
    raw = path.read_bytes()
    hashes[str(path.relative_to(repo))] = sha(raw)
    for match in pattern.finditer(raw.decode()):
        for dep in match.group(1).split():
            walk(dep)
walk('DiophantineConsistency.ModelDifferenceRing')
assert not missing, sorted(missing)
assert len(hashes) == 19
assert leaves and all(name.startswith('Mathlib.') for name in leaves), sorted(leaves)
assert 'Mathlib.Tactic.Linarith' in leaves
# This is a package source scan, not a compiled import/provider or axiom check.
mathlib = repo / '.lake/packages/mathlib/Mathlib'
mathlib_count = 0
foundation_importers = []
for path in mathlib.rglob('*.lean'):
    mathlib_count += 1
    if any(re.search(r'\bFoundation(?:\.|\b)', m.group(1)) for m in pattern.finditer(path.read_text())):
        foundation_importers.append(str(path.relative_to(repo)))
assert mathlib_count > 1000
assert not foundation_importers, foundation_importers
out = {
    'scope': 'source-only; no Lean elaboration or provider/axiom authentication',
    'candidate_change': 'prepend one Foundation.FirstOrder.Arithmetic.IOpen.Basic import',
    'original_sha256': sha(orig),
    'candidate_sha256': sha(alternative),
    'arithmetic_signed_pairs_sha256': sha(precedent.read_bytes()),
    'foundation_source_paths_and_sha256': {str(p): sha(p.read_bytes()) for p in (basic, schemata)},
    'model_difference_ring_project_closure_source_sha256': dict(sorted(hashes.items())),
    'model_difference_ring_nonproject_import_leaves': sorted(leaves),
    'missing_project_sources': sorted(missing),
    'mathlib_lean_source_files_scanned': mathlib_count,
    'mathlib_foundation_importers': foundation_importers,
}
print(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False))
