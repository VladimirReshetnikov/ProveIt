#!/usr/bin/env python3
"""Generate Lean proofs of source-to-physical per-site coverage blocks."""
import argparse
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--start-site', type=int, default=0)
p.add_argument('--stop-site', type=int, default=3673)
p.add_argument('--batch-size', type=int, default=10)
a = p.parse_args()
if not (0 <= a.start_site < a.stop_site <= 3673 and a.batch_size > 0):
    raise SystemExit('invalid source-site range or batch size')
a.out.mkdir(parents=True, exist_ok=True)
batches = []
for first in range(a.start_site, a.stop_site, a.batch_size):
    last = min(first + a.batch_size, a.stop_site)
    module = f'PA194CoverageBatch{first:04d}_{last:04d}'
    content = f'''import PA194CheckCoverage
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {module}
open PA194CheckCoverage

theorem verified : blockCheck {first} {last - first} = true := by decide +kernel
#print axioms verified
end {module}
'''
    (a.out / f'{module}.lean').write_text(content)
    batches.append((module, first, last))
if a.start_site == 0:
    imports = '\n'.join('import ' + name for name, _, _ in batches)
    proof = []
    counter = [0]
    def emit_tree(items, indent):
        if len(items) == 1:
            name, _, _ = items[0]
            proof.append(f'{indent}exact block_sound {name}.verified (by omega) (by omega)')
            return
        mid = len(items) // 2
        boundary = items[mid][1]
        ident = counter[0]
        counter[0] += 1
        proof.append(f'{indent}by_cases h{ident} : i < {boundary}')
        proof.append(f'{indent}·')
        emit_tree(items[:mid], indent + '  ')
        proof.append(f'{indent}·')
        emit_tree(items[mid:], indent + '  ')
    emit_tree(batches, '  ')
    content = f'''import PA194CoverageConditional
{imports}
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194CoverageComplete
open M6.Zip M6.Source PA194SourceProgram PA194RuntimeEngine PA194PrimitiveSimulation
open PA194CheckCoverage PA194CoverageConditional

theorem checks : ∀ i, i < {a.stop_site} → checkAt i = true := by
  intro i hi
''' + '\n'.join(proof) + '\n'
    if a.stop_site == 3673:
        content += '''
/-- Every exact source instruction has a verified physical implementation. -/
theorem coverage : PA194CompilerCorrectness.Coverage sites path 3673 :=
  PA194CoverageConditional.coverage checks

/-- Standard-Lean transfer from source nonhalting to the exact unfolded parent. -/
theorem source_nonhalt_to_parent (i n : Nat) (vs : List Nat)
    (hi : i < 3673) (hv : 10 ≤ vs.length)
    (hn : ¬CycleHalts sites ⟨.at i, readFile vs⟩) :
    ¬Halts machine (frame (path i) n vs) :=
  PA194CoverageConditional.source_nonhalt_to_parent checks i n vs hi hv hn

#print axioms coverage
#print axioms source_nonhalt_to_parent
'''
    content += '\n#print axioms checks\nend PA194CoverageComplete\n'
    (a.out / 'PA194CoverageComplete.lean').write_text(content)
print(f'Generated {len(batches)} Lean coverage blocks, formal source sites {a.start_site}..{a.stop_site - 1}')
