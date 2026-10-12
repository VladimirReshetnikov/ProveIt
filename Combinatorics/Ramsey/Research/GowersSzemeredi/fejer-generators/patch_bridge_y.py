"""Bridge + audit: Theorem 18.1 thresholds one lower (Notes L.16p)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineZ\n'
assert imp in s and 'Proofs18CoverFejerHeadlineY' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineY\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = '\n/-! ### The partition constant charged at `2^(k+9)` (Notes L.16p) -/\n\n'
for c, lo, name in ((2, 15, 'd2_fifteen'), (3, 10, 'd3_ten'), (4, 7, 'd4_seven')):
    ADD += f'''/-- **Theorem 18.1 at every degree `d ≥ {lo}` with `d + {c}` in place of `d + 10`.** -/
theorem theorem_18_1_{name}_le {{d : Nat}} (hd : {lo} ≤ d) : Theorem181AtSharp {c} d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_{name}_le_of_profiles_poly
{EXPL} hpp hp hK hpB hd

'''
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 18 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ d, 15 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_fifteen_le hd
example : ∀ d, 10 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 3 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d3_ten_le hd
example : ∀ d, 7 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_seven_le hd
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_fifteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_ten_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_seven_le
  ]''', 1)
c = 'd+2 (d >= 16) and L+0 (L >= 18); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'd+2 (d >= 16) and L+0 (L >= 18), and with the partition constant at 2^(k+9) d+2 (d >= 15), d+3 (d >= 10), d+4 (d >= 7); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
