"""Bridge + audit: Theorem 16.2 at tDegZ, Corollary 16.11 with joint slices (Notes L.16u)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineK\n'
assert imp in s and 'Proofs16PolynomialFejerJ' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs16PolynomialFejerJ\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = f'''
/-! ### Theorem 16.2 at the exact table to `14`, Corollary 16.11 with joint slices (Notes L.16u) -/

/-- **Theorem 16.2 with polynomial controls at the classes `tDegZ`.** -/
theorem theorem_16_2_polynomial_fejerZ {{k : Nat}} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegZ k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegZ k)) :=
  theorem_16_2_polynomial_fejerZ_of_profiles
{EXPL} hk

/-- **Corollary 16.11 with exponent `(2/α)^(-2^(2·tDegZ k + 7k + 38))`** (joint slices). -/
theorem corollary_16_11_polynomial_fejerJ {{k : Nat}} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 * tDegZ k + 7 * k + 38)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerJ_of_profiles
{EXPL} hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegJ_tight_le k), hN⟩
'''
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + '\nend LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 8 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_eight_le
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegZ k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegZ k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerZ hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 * LeanProofs.GowersSzemeredi.tDegZ k + 7 * k + 38)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJ hk
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_eight_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_eight_le,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerZ,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJ
  ]''', 1)
c = 'k+1 (k >= 11), k+2 (k >= 8); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'k+1 (k >= 11), k+2 (k >= 8), and the polynomial Theorem 16.2 at the exact table to 14 '
              'and Corollary 16.11 with joint slices (exponent 2^(2 tDegZ k + 7k + 38)); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
