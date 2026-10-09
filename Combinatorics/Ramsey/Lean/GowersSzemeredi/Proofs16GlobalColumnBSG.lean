import GowersSzemeredi.Proofs16ColumnZeroLadder
import GowersSzemeredi.Proofs16GlobalExactColumnQuadruples

/-! The abstract BSG engine applied to the original dense bihomomorphism.

J.98 (`global_many_exact_column_quadruples`) produces a column system with
many exact column identities. This module turns those identities into the
largeness hypothesis of `column_bsg_core` and checks its remaining inputs.
* `exact_quadruples_le_diffGoodCount`: an exact quadruple `q` with
  `q₀ + q₁ = q₂ + q₃` is a level-1 zero relation `(q₀, q₂, q₃, q₁)`.
  Fibering by `d = q₀ − q₂` injects the exact quadruples into the
  difference counts.
* `column_bsg_of_exact_quadruples`: `γN³` exact quadruples at radius `ρ₁`,
  doubling `K` and `γ|X| ≥ 4` give the conclusion of `column_bsg_core`
  with `c = γ`.
* `global_column_bsg`: from a dense `E`-bihomomorphism, with `N` above an
  explicit threshold, there is a dense set of columns. Each lies in
  `θ|X|²` additive quadruples that are exact zero relations at level 16.
  The doubling constant is `K = 2/α`, from `|X| ≥ αN/2`. No model packing
  or elimination is used. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- **Exact identities are level-1 zero relations.** -/
theorem exact_quadruples_le_diffGoodCount {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (D : Nat) (ρ₀ ρ₁ : Real) :
    ((exactColumnQuadruples X T L ρ₁).card : Real) ≤
      ∑ d ∈ X - X, (diffGoodCount X (columnZeroQ X T L D ρ₀ ρ₁ 1) d : Real) := by
  have hmaps : ∀ q ∈ exactColumnQuadruples X T L ρ₁, q 0 - q 2 ∈ X - X := by
    intro q hq
    have hX := (Finset.mem_filter.mp hq).2.1
    exact Finset.sub_mem_sub (hX 0) (hX 2)
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun q : Fin 4 → ZMod N => q 0 - q 2)
    (t := X - X) hmaps
  have hle : ∀ d ∈ X - X, ((exactColumnQuadruples X T L ρ₁).filter fun q => q 0 - q 2 = d).card ≤
      diffGoodCount X (columnZeroQ X T L D ρ₀ ρ₁ 1) d := by
    intro d _
    have key := Finset.card_le_card_of_injOn (fun q : Fin 4 → ZMod N => (q 2, q 1))
      (s := (exactColumnQuadruples X T L ρ₁).filter fun q => q 0 - q 2 = d)
      (t := (X ×ˢ X).filter fun p => p.1 + d ∈ X ∧ p.2 + d ∈ X ∧
        columnZeroQ X T L D ρ₀ ρ₁ 1 (p.1 + d) p.1 (p.2 + d) p.2) ?_ ?_
    · refine key.trans (le_of_eq ?_)
      unfold diffGoodCount
      congr 1
      ext p
      simp only [Finset.mem_filter]
    · intro q hq
      obtain ⟨hqE, hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hX, hadd, hid⟩ := Finset.mem_filter.mp hqE
      unfold IsAdditiveQuadruple at hadd
      have h0 : q 2 + d = q 0 := by rw [← hd]; ring
      have h3 : q 1 + d = q 3 := by rw [← hd]; linear_combination hadd
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hX 2, hX 1⟩, ?_, ?_, ?_⟩
      · simp only; rw [h0]; exact hX 0
      · simp only; rw [h3]; exact hX 3
      · simp only; rw [h0, h3]
        refine ⟨hX 0, hX 2, hX 3, hX 1, by linear_combination hadd, fun y hy => ?_⟩
        have hall : ∀ i, y ∈ bohr (T (q i)) (zeroLadderRadius D ρ₀ ρ₁ 0) := by
          intro i
          refine bohr_anti ?_ _ hy
          intro t ht
          simp only [quadSpec, Finset.mem_union]
          fin_cases i <;> simp_all
        have := hid y hall
        unfold columnAlt
        linear_combination this
    · intro q hq q' hq' h
      obtain ⟨hqE, hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqE', hd'⟩ := Finset.mem_filter.mp hq'
      have hadd := (Finset.mem_filter.mp hqE).2.2.1
      have hadd' := (Finset.mem_filter.mp hqE').2.2.1
      unfold IsAdditiveQuadruple at hadd hadd'
      simp only [Prod.mk.injEq] at h
      obtain ⟨h2, h1⟩ := h
      have h0 : q 0 = q' 0 := by
        have e1 : q 0 = d + q 2 := by rw [← hd]; ring
        have e2 : q' 0 = d + q' 2 := by rw [← hd']; ring
        rw [e1, e2, h2]
      have h3 : q 3 = q' 3 := by linear_combination hadd' - hadd + h0 + h1 - h2
      funext i
      fin_cases i <;> simp_all
  calc ((exactColumnQuadruples X T L ρ₁).card : Real)
      = ∑ d ∈ X - X, (((exactColumnQuadruples X T L ρ₁).filter fun q => q 0 - q 2 = d).card : Real) := by
        exact_mod_cast hfib
    _ ≤ _ := Finset.sum_le_sum fun d hd => by exact_mod_cast hle d hd

/-- **The column BSG core from exact column identities.** -/
theorem column_bsg_of_exact_quadruples {N : Nat} [NeZero N] [Fact N.Prime] (hN2 : N ≠ 2)
    {X : Finset (ZMod N)} (hX : X.Nonempty)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) {D : Nat} (hD : 1 ≤ D)
    {ρ₀ ρ₁ : Real} (h₀ : 0 < ρ₀) (h₀1 : ρ₀ ≤ 1) (h₁ : 0 < ρ₁) (h₁₀ : ρ₁ ≤ ρ₀)
    (hcol : ∀ x ∈ X, (T x).card ≤ D ∧ IsFreimanLinearOn (bohr (T x) ρ₀) (L x) ∧ L x 0 = 0)
    (hN : refinementKernelCap (4 * D) (2 * D) ρ₀ (zeroLadderRadius D ρ₀ ρ₁ 14) < N)
    {γ K θ : Real} (hγ : 0 < γ) (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hexact : γ * (N : Real) ^ 3 ≤ (exactColumnQuadruples X T L ρ₁).card)
    (hγX : 4 ≤ γ * X.card) (hθ : θ < absBsgKappa γ K / 2) :
    ∃ B B' : Finset (ZMod N), B' ⊆ B ∧ B ⊆ X ∧ absBsgEps γ K * X.card ≤ (B'.card : Real) ∧
      ∀ a ∈ B', θ * (X.card : Real) ^ 2 ≤ richCount B (columnZeroQ X T L D ρ₀ ρ₁ 16) a := by
  have hXN : (X.card : Real) ≤ N := by
    have : X.card ≤ N := by
      calc X.card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ X
        _ = N := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast this
  have hgood : γ * (X.card : Real) ^ 3 ≤
      ∑ d ∈ X - X, (diffGoodCount X (columnZeroQ X T L D ρ₀ ρ₁ 1) d : Real) := by
    calc γ * (X.card : Real) ^ 3 ≤ γ * (N : Real) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hXN 3) hγ.le
      _ ≤ _ := hexact
      _ ≤ _ := exact_quadruples_le_diffGoodCount X T L D ρ₀ ρ₁
  exact column_bsg_core hN2 (subset_refl X) hX T L hD h₀ h₀1 h₁ h₁₀ hcol hN hγ hK hdoub hgood
    hγX hθ

/-- The modulus threshold of `global_column_bsg`. -/
def globalColumnBSGModulusBound (alpha : Real) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  max 3 (max (globalColumnIdentityModulusBound alpha)
    (max (refinementKernelCap (4 * d) (2 * d) (1 / (4 * Real.pi))
      (zeroLadderRadius d (1 / (4 * Real.pi)) (globalColumnIdentityRadius alpha) 14) + 1)
      ⌈8 / (alpha * globalColumnQuadrupleDensity alpha)⌉₊))

/-- **The abstract BSG engine on the original dense bihomomorphism.** -/
theorem global_column_bsg {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha θ : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnBSGModulusBound alpha ≤ N)
    (hθ : θ < absBsgKappa (globalColumnQuadrupleDensity alpha) (2 / alpha) / 2) :
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
      (B B' : Finset (ZMod N)),
      alpha / 2 * N ≤ X.card ∧
      (∀ x ∈ X, (T x).card ≤ columnSpectrumCap (columnEightDensity alpha) ∧
        IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x) ∧ L x 0 = 0) ∧
      B' ⊆ B ∧ B ⊆ X ∧
      absBsgEps (globalColumnQuadrupleDensity alpha) (2 / alpha) * X.card ≤ (B'.card : Real) ∧
      ∀ a ∈ B', θ * (X.card : Real) ^ 2 ≤ richCount B
        (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
          (globalColumnIdentityRadius alpha) 16) a := by
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
  have hdoub : ((X - X).card : Real) ≤ 2 / alpha * X.card := by
    have h1 : ((X - X).card : Real) ≤ N := by
      have : (X - X).card ≤ N := by
        calc (X - X).card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
          _ = N := by rw [Finset.card_univ, ZMod.card]
      exact_mod_cast this
    have h2 : (N : Real) ≤ 2 / alpha * X.card := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith
    linarith
  have hγX : 4 ≤ globalColumnQuadrupleDensity alpha * X.card := by
    have hceil : 8 / (alpha * globalColumnQuadrupleDensity alpha) ≤ (N : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hNγ)
    have h8 : 8 ≤ alpha * globalColumnQuadrupleDensity alpha * N := by
      rw [div_le_iff₀ (by positivity)] at hceil; linarith
    nlinarith
  have hd : 1 ≤ columnSpectrumCap (columnEightDensity alpha) :=
    Nat.ceil_pos.mpr (by have := columnEightDensity_pos ha; positivity)
  have hρle : globalColumnIdentityRadius alpha ≤ 1 / (4 * Real.pi) :=
    globalColumnIdentityRadius_le ha ha1
  have hρ₀ : (0 : Real) < 1 / (4 * Real.pi) := by positivity
  have hρ₀1 : 1 / (4 * Real.pi) ≤ (1 : Real) := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hexact : globalColumnQuadrupleDensity alpha * (N : Real) ^ 3 ≤
      (exactColumnQuadruples X T L (globalColumnIdentityRadius alpha)).card := hcount
  obtain ⟨B, B', hB'B, hBX, hsize, hrich⟩ := column_bsg_of_exact_quadruples (by omega) hXne T L
    hd hρ₀ hρ₀1 hρ hρle (fun x hx => ⟨hT x hx, hL x hx, hzero x hx⟩) hNcap hγ
    (by positivity) hdoub hexact hγX hθ
  exact ⟨X, T, L, B, B', hXlow, fun x hx => ⟨hT x hx, hL x hx, hzero x hx⟩, hB'B, hBX, hsize,
    hrich⟩

end LeanProofs.GowersSzemeredi
