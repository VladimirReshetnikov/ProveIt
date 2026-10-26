from pathlib import Path
import argparse, difflib, json

OUT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, default=OUT.parents[1] / 'ProveIt',
                    help='checkout of ProveIt at the pinned baseline')
args = parser.parse_args()
SRC = args.repo / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PREFIX = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'

def declaration_span(text, name, next_marker):
    a = text.index(name)
    b = text.index(next_marker, a)
    return a, b

def patch_file(name, old, new, output):
    output.write_text(''.join(difflib.unified_diff(
        old.splitlines(keepends=True), new.splitlines(keepends=True),
        fromfile='a/' + PREFIX + name, tofile='b/' + PREFIX + name)))
    (OUT / 'modified').mkdir(exist_ok=True)
    (OUT / 'modified' / name).write_text(new)
    return {'file': name, 'old_lines': len(old.splitlines()), 'new_lines': len(new.splitlines()),
            'lines_saved': len(old.splitlines()) - len(new.splitlines())}

metrics = []
name = 'NativePellStepDown.lean'
odd_old = (SRC / name).read_text()
odd_new = odd_old.replace('import Diophantine.Paper1980.PellHalf90\n',
    'import Diophantine.Paper1980.PellHalf90\n'
    'import DiophantineConsistency.SignedPellResidue\n', 1)
a = odd_new.index('  have hs0 : 0 < s := by')
b = odd_new.index('  have hIZ0 :', a)
odd_new = odd_new[:a] + odd_new[b:]
a = odd_new.index('  have hsodd : Odd s := by')
b = odd_new.index('  obtain ⟨h, hs⟩ := hsodd', a)
odd_new = odd_new[:a] + '''  have hsodd : Odd s := SignedPellResidue.odd_index_of_base_dvd hI1 (by
    rw [← hIu]
    exact dvd_mul_right I u)
''' + odd_new[b:]
odd_metrics = patch_file(name, odd_old, odd_new, OUT / 'pell-oddness-only.patch')

name = 'CurrentCellLabels2011.lean'
old = (SRC / name).read_text()
a, b = declaration_span(old, 'theorem sum_le_one_cases', '\ntheorem Selected.weighted_sum')
replacement = (OUT / 'OneHotSupport.lean').read_text()
x, y = declaration_span(replacement, 'theorem sum_le_one_cases', '\n#print axioms')
new = old[:a] + replacement[x:y] + old[b:]
metrics.append(patch_file(name, old, new, OUT / 'one-hot-support.patch'))

name = 'NativePellStepDown.lean'
old = (SRC / name).read_text()
new = old.replace('import Diophantine.Paper1980.PellHalf90\n',
    'import Diophantine.Paper1980.PellHalf90\n'
    'import DiophantineConsistency.SignedPellResidue\n'
    'import DiophantineConsistency.ProofSimplification.SignedModEq\n', 1)
a = new.index('  have hs0 : 0 < s := by')
b = new.index('  have hIZ0 :', a)
new = new[:a] + new[b:]
a = new.index('  have hsodd : Odd s := by')
b = new.index('  obtain ⟨h, hs⟩ := hsodd', a)
new = new[:a] + '''  have hsodd : Odd s := SignedPellResidue.odd_index_of_base_dvd hI1 (by
    rw [← hIu]
    exact dvd_mul_right I u)
''' + new[b:]
a = new.index('  have hJs : (J : ℤ) ≡')
b = new.index('\n/-- The same index residues', a)
new = new[:a] + '''  exact ProofSimplification.signed_index_chase hu_J hu_cc
    (neg_one_pow_eq_or ℤ h) hsp'
''' + new[b:]
a = new.index('  have hvJ : (V.natAbs : ℤ) ≡')
b = new.index('  exact index_residues', a)
new = new[:a] + '''  have hvJ : (V.natAbs : ℤ) ≡ J [ZMOD c] ∨
      (V.natAbs : ℤ) ≡ -(J : ℤ) [ZMOD c] :=
    (ProofSimplification.SignedModEq.natAbs c V).trans (Or.inr hVJ)
''' + new[b:]
metrics.append(patch_file(name, old, new, OUT / 'pell-sign-algebra.patch'))

name = 'SignedPellResidue.lean'
old = (SRC / name).read_text()
new = old.replace('import Diophantine.Common.PellInt\n',
    'import Diophantine.Common.PellInt\n'
    'import DiophantineConsistency.ProofSimplification.SignedModEq\n', 1)
a = new.index('  by_cases hy0 : 0 ≤ y')
b = new.index('\n/-- The full signed residue', a)
new = new[:a] + '''  exact ProofSimplification.signed_of_natAbs habs
''' + new[b:]
metrics.append(patch_file(name, old, new, OUT / 'signed-pell-natabs.patch'))

helper = (OUT / 'SignedModEq.lean').read_text()
helper = '\n'.join(line for line in helper.splitlines() if not line.startswith('#print axioms')) + '\n'
(OUT / 'modified' / 'SignedModEq.lean').write_text(helper)
(OUT / 'new-helper.patch').write_text(''.join(difflib.unified_diff(
    [], helper.splitlines(keepends=True), fromfile='/dev/null',
    tofile='b/' + PREFIX + 'ProofSimplification/SignedModEq.lean')))
(OUT / 'combined.patch').write_text(''.join((OUT / p).read_text() for p in [
    'new-helper.patch', 'one-hot-support.patch', 'pell-sign-algebra.patch',
    'signed-pell-natabs.patch']))
(OUT / 'metrics.json').write_text(json.dumps({'files': metrics,
    'alternative_oddness_only': odd_metrics,
    'helper_lines': len(helper.splitlines()),
    'net_lines_saved_with_helper': sum(m['lines_saved'] for m in metrics) - len(helper.splitlines())}, indent=2) + '\n')
print(json.dumps(json.loads((OUT / 'metrics.json').read_text()), indent=2))
