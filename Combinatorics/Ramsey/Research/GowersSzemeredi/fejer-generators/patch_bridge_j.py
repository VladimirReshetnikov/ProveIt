"""Bridge + audit: joint slices (Notes L.16q)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineY\n'
assert imp in s and 'Proofs18CoverFejerHeadlineJ' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineJ\n'
              'import GowersSzemeredi.Proofs18CoverFejerLowDegrees4\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = '\n/-! ### Joint slices (Notes L.16q) -/\n\n'
for c, lo, name in ((2, 12, 'd2_twelve'), (3, 9, 'd3_nine'), (4, 4, 'd4_four')):
    ADD += f'''/-- **Theorem 18.1 at every degree `d ≥ {lo}` with `d + {c}` in place of `d + 10`.** -/
theorem theorem_18_1_{name}_le {{d : Nat}} (hd : {lo} ≤ d) : Theorem181AtSharp {c} d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_{name}_le_of_profiles_poly
{EXPL} hpp hp hK hpB hd

'''
ADD += '''/-- **Theorem 18.1 at every degree with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d := by
  match d with
  | 0 => exact theorem_18_1_d4_degree_zero
  | 1 => exact theorem_18_1_d4_degree_one
  | 2 => exact theorem_18_1_d4_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
    exact theorem_18_1_d4_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact theorem_18_1_d4_four_le (by omega)

'''
for c, lo, word in ((0, 15, 'fifteen'), (1, 12, 'twelve'), (2, 9, 'nine')):
    ADD += f'''/-- **Theorem 18.2 at every length `L ≥ {lo}` with `L + {c}` in place of `L + 9`.** -/
theorem theorem_18_2_L{c}_{word}_le {{L : Nat}} (hL : {lo} ≤ L) : Theorem182AtSharp {c} L :=
  theorem_18_2_L{c}_{word}_le_of_profiles_poly
{EXPL} hL

/-- **Corollary 18.7 at every length `L ≥ {lo}` with `L + {c}`.** -/
theorem corollary_18_7_L{c}_{word}_le {{L : Nat}} (hL : {lo} ≤ L) : Corollary187AtSharp {c} L :=
  (theorem_18_2_L{c}_{word}_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ {lo}` and `r ≥ 2`, the bound of
Theorem 1.3 with `k + {c}`. -/
theorem van_der_waerden_L{c}_{word}_le {{k : Nat}} (hk : {lo} ≤ k) {{r : Nat}} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt {c} (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L{c}_{word}_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with `k + {c}` for every `k ≥ {lo}`.** -/
theorem theorem_1_3_L{c}_{word}_le : Theorem13AtFrom {c} {lo} :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L{c}_{word}_le hk

'''
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : ∀ d, 7 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_seven_le hd
'''
assert s.count(a) == 1
PIN = ''
for c, lo, name in ((2, 12, 'd2_twelve'), (3, 9, 'd3_nine'), (4, 4, 'd4_four')):
    PIN += f'''example : ∀ d, {lo} ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp {c} d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_{name}_le hd
'''
PIN += '''example : ∀ d, LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d4
'''
NAMES = ['theorem_18_1_d2_twelve_le', 'theorem_18_1_d3_nine_le', 'theorem_18_1_d4_four_le', 'theorem_18_1_d4']
for c, lo, word in ((0, 15, 'fifteen'), (1, 12, 'twelve'), (2, 9, 'nine')):
    PIN += f'''example : ∀ L, {lo} ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp {c} L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L{c}_{word}_le hL
example : ∀ L, {lo} ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp {c} L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L{c}_{word}_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom {c} {lo} :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L{c}_{word}_le
'''
    NAMES += [f'theorem_18_2_L{c}_{word}_le', f'corollary_18_7_L{c}_{word}_le',
              f'van_der_waerden_L{c}_{word}_le', f'theorem_1_3_L{c}_{word}_le']
s = s.replace(a, a + PIN, 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_seven_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_seven_le,\n'
              + ',\n'.join(f'    ``LeanProofs.GowersSzemeredi.{n}' for n in NAMES) + '\n  ]', 1)
c = 'd+2 (d >= 15), d+3 (d >= 10), d+4 (d >= 7); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'd+2 (d >= 15), d+3 (d >= 10), d+4 (d >= 7), and with joint slices d+2 (d >= 12), '
              'd+3 (d >= 9), d+4 in every degree, L+0 (L >= 15), L+1 (L >= 12), L+2 (L >= 9) with the '
              'van der Waerden bound and Theorem 1.3 at k (k >= 15), k+1 (k >= 12), k+2 (k >= 9); '
              'only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
