"""Bridge + audit: polynomial Theorem 16.2 / Corollary 16.11 at the X classes (Notes L.16n)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineX\n'
assert imp in s and 'Proofs16PolynomialFejerX' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs16PolynomialFejerX\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = '''
/-- **Theorem 16.2 with polynomial controls at the classes of constant `5/2`**, in
every dimension `k ≥ 1`: graph count `max(1, (4V/(γθρ))^uDegX k)` with
`V = 2^(2^(4k+13))` and `log₂ uDegX k = tDegX k` (`5·2^(k−1) + O(k²)`; printed
`68·2^k`). -/
theorem theorem_16_2_polynomial_fejerX {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegX k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegX k)) :=
  theorem_16_2_polynomial_fejerX_of_profiles
EXPL hk

/-- **Corollary 16.11 with polynomial exponents at the classes of constant `5/2`**,
in every dimension `k + 1 ≥ 3`: `e⁻¹ ≤ (2/α)^(2^(3·tDegX k + 6k + 38))`, that is
`7.5·2^k + O(k²)` (printed route `236·2^k`). -/
theorem corollary_16_11_polynomial_fejerX {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (3 * tDegX k + 6 * k + 38)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerX_of_profiles
EXPL hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegX_tight_le k), hN⟩

'''.replace('EXPL', EXPL)
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 19 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegX k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegX k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerX hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (3 * LeanProofs.GowersSzemeredi.tDegX k + 6 * k + 38)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX hk
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerX,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX
  ]''', 1)
c = 'with the van der Waerden bound and Theorem 1.3 at k (k >= 19); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'with the van der Waerden bound and Theorem 1.3 at k (k >= 19), and the polynomial Theorem 16.2 / Corollary 16.11 at those classes; only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
