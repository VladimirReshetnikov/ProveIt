"""Bridge + audit: d+2 from degree 16, L+0 from length 18 (Notes L.16o)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs16PolynomialFejerX\n'
assert imp in s and 'Proofs18CoverFejerHeadlineZ' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineZ\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = '''
/-! ### The exact class table to dimension `14` (Notes L.16o) -/

/-- **Theorem 18.1 at every degree `d ≥ 16` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_sixteen_le {d : Nat} (hd : 16 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_sixteen_le_of_profiles_poly
EXPL hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 18` with no offset.** -/
theorem theorem_18_2_L0_eighteen_le {L : Nat} (hL : 18 ≤ L) : Theorem182AtSharp 0 L :=
  theorem_18_2_L0_eighteen_le_of_profiles_poly
EXPL hL

/-- **Corollary 18.7 at every length `L ≥ 18` with no offset.** -/
theorem corollary_18_7_L0_eighteen_le {L : Nat} (hL : 18 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_eighteen_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 18` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0_eighteen_le {k : Nat} (hk : 18 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_eighteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 18`.** -/
theorem theorem_1_3_L0_eighteen_le : Theorem13AtFrom 0 18 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_eighteen_le hk

'''.replace('EXPL', EXPL)
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX hk
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ d, 16 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_sixteen_le hd
example : ∀ L, 18 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L0_eighteen_le hL
example : ∀ L, 18 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L0_eighteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 18 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_sixteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le
  ]''', 1)
c = 'and the polynomial Theorem 16.2 / Corollary 16.11 at those classes; only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'and the polynomial Theorem 16.2 / Corollary 16.11 at those classes, and with the exact table to dimension 14 d+2 (d >= 16) and L+0 (L >= 18); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
