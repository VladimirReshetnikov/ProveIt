"""Bridge, audit and docs: Theorem 16.2 and Corollary 16.11 at tDegT3 (Notes L.16y)."""
import sys
from pathlib import Path

R = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey')
GS = R / 'Lean/GowersSzemeredi'
mode = sys.argv[1]
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
if mode == 'lean':
    p = GS / 'Proofs18CoverFejerAllDegrees.lean'
    s = p.read_text(encoding='utf-8')
    imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineK3\n'
    assert imp in s and 'Proofs16PolynomialFejerT3' not in s
    s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs16PolynomialFejerT3\n', 1)
    s = s.replace('\nend LeanProofs.GowersSzemeredi', f'''
/-! ### Theorem 16.2 and Corollary 16.11 at the tight two-track classes (Notes L.16y) -/

/-- **Theorem 16.2 with polynomial controls at the classes `tDegT3`.** -/
theorem theorem_16_2_polynomial_fejerT3 {{k : Nat}} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k)) :=
  theorem_16_2_polynomial_fejerT3_of_profiles
{EXPL} hk

/-- **Corollary 16.11 with exponent `(2/α)^(-2^(2·tDegT3 k + 7k + 38))`.** -/
theorem corollary_16_11_polynomial_fejerJT3 {{k : Nat}} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 * tDegT3 k + 7 * k + 38)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerJT3_of_profiles
{EXPL} hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegJT3_tight_le k), hN⟩

end LeanProofs.GowersSzemeredi''')
    p.write_text(s, encoding='utf-8', newline='\n')
    p = GS / 'CompletionAudit.lean'
    s = p.read_text(encoding='utf-8')
    a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le
'''
    assert s.count(a) == 1
    s = s.replace(a, a + '''example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegT3 k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegT3 k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerT3 hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 * LeanProofs.GowersSzemeredi.tDegT3 k + 7 * k + 38)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJT3 hk
''', 1)
    b = '    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le\n  ]'
    assert s.count(b) == 1
    s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerT3,\n'
                  '    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJT3\n  ]', 1)
    c = 'Theorem 1.3 at k (k >= 13); only approved axioms."'
    assert s.count(c) == 1
    s = s.replace(c, 'Theorem 1.3 at k (k >= 13), and the polynomial Theorem 16.2 and Corollary 16.11 at the '
                  'tight two-track classes; only approved axioms."', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('lean patched')
else:
    p = R / 'Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md'
    s = p.read_text(encoding='utf-8')
    anchor = "`2^(-2^k)` for `k ≥ 13`. Theorem 18.1 does not move.\n"
    assert s.count(anchor) == 1
    s = s.replace(anchor, anchor + '''The polynomial Theorem 16.2 and Corollary 16.11 move with the class table:
`Proofs16PolynomialFejerT3` (`assemble_polyt3.py`) gives Theorem 16.2 with graph
count exponent `2^tDegT3 k` and Corollary 16.11 with
`e⁻¹ ≤ (2/α)^(2^(2·tDegT3 k + 7k + 38))` (`theorem_16_2_polynomial_fejerT3`,
`corollary_16_11_polynomial_fejerJT3`). `tDegT3` is 6–22% below `tDegZ` in
dimensions 3–14.
''', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'FORMALIZATION_STATUS.txt'
    s = p.read_text(encoding='utf-8')
    a = "  van_der_waerden_L0_thirteen_le, theorem_1_3_L0_thirteen_le. Stub-checked and pinned.\n"
    assert s.count(a) == 1
    s = s.replace(a, a + """  Polynomial Theorem 16.2 / Corollary 16.11 at tDegT3 (Proofs16PolynomialFejerT3):
  theorem_16_2_polynomial_fejerT3, corollary_16_11_polynomial_fejerJT3
  (exponent 2^(2 tDegT3 k + 7k + 38)). Stub-checked and pinned.
""", 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'Research/GowersSzemeredi/joint-vertex-covers/joint-vertex-covers.tex'
    s = p.read_text(encoding='utf-8')
    x = r'''\item the corollary has $e^{-1}\le(2/\alpha)^{2^{2t_k+7k+38}}$, that is
  $5\cdot2^k+O(k^2)$\\ (\lean{corollary\_16\_11\_polynomial\_fejerJ}).
\end{itemize}'''
    assert s.count(x) == 1
    s = s.replace(x, x + r'''
At the two-track classes from the tight dimension-two count, the table $t_k$
is a further 6--22\% lower in dimensions $3$ to $14$
(\lean{theorem\_16\_2\_polynomial\_fejerT3}, \lean{corollary\_16\_11\_polynomial\_fejerJT3}).''', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('docs patched')
