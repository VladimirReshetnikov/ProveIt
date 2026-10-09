import GowersSzemeredi.Proofs16GlobalColumnBSG
import GowersSzemeredi.Proofs16AbstractBSGWordSystem

/-! Compatible word representations for the original dense bihomomorphism.

`abstract_bsg_word_system` (J.142) gives word representations for any
quadruple ladder on `ℤ/N` with the BSG hypotheses. Instantiate it with the
exact zero-relation ladder `columnZeroQ` of J.98's column system:
* weak transitivity: `columnZeroQ_weakTransitive` holds with every
  `c′ > 0` against `c′|X|`, and `|X| ≤ N`;
* doubling over all of `ℤ/N`, with `K = 1`;
* largeness: the `γN³` exact identities of J.98 (via
  `exact_quadruples_le_diffGoodCount`), with
  `γ = globalColumnQuadrupleDensity α`.

`global_column_word_system` returns dense `B′ ⊆ B ⊆ X` with threshold
richness, and the compatible word representations of every anchor list of
length at most `k + 1` in `B′`. Every relation is an exact level-16 zero
relation of the column maps, and every loss is polynomial in `γ` at fixed
`k`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- **Word representations for the column system of a dense bihomomorphism.** -/
theorem global_column_word_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnBSGModulusBound alpha ≤ N) (k : Nat) :
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
      (B B' : Finset (ZMod N)),
      alpha / 2 * N ≤ X.card ∧
      (∀ x ∈ X, (T x).card ≤ columnSpectrumCap (columnEightDensity alpha) ∧
        IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x) ∧ L x 0 = 0) ∧
      B' ⊆ B ∧ B ⊆ X ∧
      absBsgEps (globalColumnQuadrupleDensity alpha) 1 * N ≤ (B'.card : Real) ∧
      ThresholdRelationRichness B
        (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
          (globalColumnIdentityRadius alpha) 16)
        (absBsgWordBeta (globalColumnQuadrupleDensity alpha) 1 k)
        (absBsgWordEta (globalColumnQuadrupleDensity alpha) 1) ∧
      ∀ a : ZMod N, ∀ as : List (ZMod N), (∀ x ∈ a :: as, x ∈ B') → as.length ≤ k →
        thresholdColumnWordDensity (absBsgWordLambda (globalColumnQuadrupleDensity alpha) 1)
            (absBsgWordEta (globalColumnQuadrupleDensity alpha) 1) as.length *
          (N : Real) ^ (3 * as.length + 2) ≤
        (relationWordRepresentations B
          (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
            (globalColumnIdentityRadius alpha) 16) (a :: as)).card := by
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : globalColumnIdentityModulusBound alpha ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNcap : refinementKernelCap (4 * columnSpectrumCap (columnEightDensity alpha))
      (2 * columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
      (zeroLadderRadius (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
        (globalColumnIdentityRadius alpha) 14) < N :=
    Nat.lt_of_succ_le ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hN)))
  have hNγ : ⌈8 / (alpha * globalColumnQuadrupleDensity alpha)⌉₊ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨X, T, L, W, hX, -, hT, hL, hzero, -, hρ, hγ, hcount⟩ :=
    global_many_exact_column_quadruples A phi ha ha1 hA hphi hN1
  set γ := globalColumnQuadrupleDensity alpha with hγdef
  set d := columnSpectrumCap (columnEightDensity alpha) with hddef
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hXlow : alpha / 2 * N ≤ X.card := by
    have h2 : alpha / 2 ≤ alpha / (2 - alpha) := by
      apply div_le_div_of_nonneg_left ha.le (by linarith) (by linarith)
    exact (mul_le_mul_of_nonneg_right h2 hNpos.le).trans hX
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < X.card := (by positivity : (0 : Real) < alpha / 2 * N).trans_le hXlow
    exact_mod_cast this
  have hXN : (X.card : Real) ≤ N := by
    have : X.card ≤ N := by
      calc X.card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ X
        _ = N := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast this
  have hd : 1 ≤ d := Nat.ceil_pos.mpr (by have := columnEightDensity_pos ha; positivity)
  have hρle : globalColumnIdentityRadius alpha ≤ 1 / (4 * Real.pi) :=
    globalColumnIdentityRadius_le ha ha1
  have hρ₀ : (0 : Real) < 1 / (4 * Real.pi) := by positivity
  have hρ₀1 : 1 / (4 * Real.pi) ≤ (1 : Real) := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x) ∧
      L x 0 = 0 := fun x hx => ⟨hT x hx, hL x hx, hzero x hx⟩
  let Q := columnZeroQ X T L d (1 / (4 * Real.pi)) (globalColumnIdentityRadius alpha)
  have hpar := absBsgWord_parameters_pos hγ zero_lt_one k
  let c' := absBsgWordTransitivity γ 1 k
  have hc' : 0 < c' := hpar.2.2.2
  have hWTX := columnZeroQ_weakTransitive (A := X) hXne T L hd hρ₀ hρ₀1 hρ hρle hcol hNcap hc'
  have hWT : ∀ i j, i + j ≤ 16 → ∀ a b e f, c' * N ≤ (((X ×ˢ X).filter fun p =>
      Q i a b p.1 p.2 ∧ Q j p.1 p.2 e f).card : Real) → Q (i + j) a b e f := by
    intro i j hij a b e f h
    exact hWTX i j hij a b e f ((mul_le_mul_of_nonneg_left hXN hc'.le).trans h)
  have hdoub : (((Finset.univ : Finset (ZMod N)) - Finset.univ).card : Real) ≤ 1 * N := by
    have : ((Finset.univ : Finset (ZMod N)) - Finset.univ).card ≤ N := by
      calc _ ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
        _ = N := by rw [Finset.card_univ, ZMod.card]
    rw [one_mul]; exact_mod_cast this
  have hgood : γ * (N : Real) ^ 3 ≤ ∑ e ∈ (Finset.univ : Finset (ZMod N)) - Finset.univ,
      (diffGoodCount X (Q 1) e : Real) := by
    calc γ * (N : Real) ^ 3 ≤ (exactColumnQuadruples X T L (globalColumnIdentityRadius alpha)).card :=
          hcount
      _ ≤ ∑ e ∈ X - X, (diffGoodCount X (Q 1) e : Real) :=
          exact_quadruples_le_diffGoodCount X T L d _ _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.sub_subset_sub (Finset.subset_univ X) (Finset.subset_univ X))
          (fun _ _ _ => by positivity)
  have hcN : 4 ≤ γ * N := by
    have hceil : 8 / (alpha * γ) ≤ (N : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hNγ)
    have h8 : 8 ≤ alpha * γ * N := by
      rw [div_le_iff₀ (by positivity)] at hceil; linarith
    nlinarith
  obtain ⟨B, B', hB'B, hBX, hsize, hrich, hwords⟩ :=
    abstract_bsg_word_system (by omega) X Q
      (columnZeroQ_S1 X T L d _ _ 1) (columnZeroQ_S2 X T L d _ _ 4)
      (fun i => columnZeroQ_S3 X T L d _ _ i) hγ hc' zero_lt_one hWT hdoub hgood hcN k le_rfl
  exact ⟨X, T, L, B, B', hXlow, hcol, hB'B, hBX, hsize, hrich, hwords⟩

end LeanProofs.GowersSzemeredi
