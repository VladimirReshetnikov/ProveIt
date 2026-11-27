import New.Congruences.FirstOrder.RibetMatrices
import New.Congruences.FirstOrder.RibetMethod

/-!
# Ribet's method to first order over a discrete valuation ring

This file proves an algebraic form of Ribet's method to first order that does not involve Galois
groups. Here `u x` (`x : Y`) is a finite family of representations of a group `G` over a discrete
valuation ring `O`; at certain `x`, `u x` is the sum of a main summand (the block) and of
characters. The file glues the matrices of tied rows for the block and for the characters, so that
one element serves the determinants of all combinations `∑ ω g (u x g - 1)`, and passes from
coefficients modulo powers of `p` to coefficients in `K/O`. The result is applied to Galois
representations in `New.Selmer.ribet_columns`.

In that application the data of `New.Selmer.exists_isCommonRibetElement_addVal_le` are as follows.
The elements `τ (j, true)` and `φ (j, true)` are a tame generator and a Frobenius element at the new
place `j`, and `τ (j, false)`, `φ (j, false)` are the inverses of their conjugates. The `δ v` are
tame generators at the old places, `γ x` acts on the summand by a scalar `y x` with `y x - 1` a
unit, `a` generates the cyclotomic quotient, `p` is `ℓ ^ ν`, and `C : O` is the cost of telling the
characters apart. The `X j` are free variables; only the coefficients of the monomials that divide
`∏ X j` are read.

## Main definitions and results

* `New.Selmer.exists_isCommonRibetElement_addVal_le`: the determinants of all combinations
  `∑ ω g (u x g - 1)` have one Ribet element whose coefficient comes from `O` and has bounded
  valuation. The proof finds matrices of tied rows with bounded determinant on the block
  (`exists_tiedRows_addVal_det_le`) and on the characters (`nonempty_characterRows`), and glues them
  (`exists_traceIdeal_multiplier_eq_sum_det`).
* `New.Selmer.exists_traceIdeal_multiplier_eq_sum_det`: the gluing, on the set where `u x` is the
  block `ρ x` plus the characters `ξ e`, with `ξ 0 = 1`.

Notions from other files:
* `New.Selmer.ribetCocyclesIn u ρ B`: the cocycles `G → B^d` for `ρ` that obey the linear relations
  among the families `(u x g - 1)_x`.
* `New.Selmer.IsCommonRibetElement` (`FittingBlock`): one `f : S` that serves as Ribet element for
  a family `β` of functions `β i : Y → L`.
* `New.Selmer.IsTraceIdeal` (`FittingBlock`): `S` holds the characteristic polynomials, and the
  `S`-module `𝒥` holds the traces of given relations.
* `New.Selmer.tiedRows` (`RibetMatrices`): the rows whose element `∑ r i (gen i - 1)` lies in the
  tie ideal.
-/

section RibetFirstOrder

namespace New.Selmer

open IsDiscreteValuationRing Matrix Module Submodule Polynomial MonoidAlgebra Finset Sum
  CompleteLattice

open Finsupp (linearCombination)

open MvPolynomial hiding X C aeval eval funext comap ext

attribute [local instance] algebraMvPolynomial

section Steps

variable {O L Y G J σ W : Type} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  [Group G] (u : Y → G →* Matrix σ σ O) {S : Subalgebra O (Y → MvPolynomial J L)}
  (𝒥 : Submodule S (Y → MvPolynomial J L))

variable {p : O} {τ φ : J × Bool → G} {ε : J → O[X]}

/-! ### The gluing -/

/-- If `u x` is, after reindexing by `blockEquiv`, the block `ρ` plus the characters `ξ e`, then so
is its extension to `O[X j][G]` (`polyAction`, and `polyChar` for the characters). -/
lemma polyAction_eq_reindex {r : Type} [Fintype r] [DecidableEq r] {t : ℕ}
    (blockEquiv : r ⊕ Fin t ≃ σ) {x : Y} {ρ : G →* Matrix r r O} {ξ : Fin t → G →* O}
    (hu : ∀ g : G, u x g = reindex blockEquiv blockEquiv
      (fromBlocks (ρ g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (c : (MvPolynomial J O)[G]) :
    polyAction J (u x) c = reindex blockEquiv blockEquiv
      (fromBlocks (polyAction J ρ c) 0 0 (diagonal fun e : Fin t ↦ polyChar J (ξ e) c)) := by
  rw [← Equiv.symm_apply_eq]
  ext1 (i | i) (j | j)
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, polyChar, hu, lift_apply, diagonal, apply_ite (Algebra.ofId O _),
      Finsupp.sum, Matrix.sum_apply]

/-- If the `z g` are coordinates of the `u · g - 1` (`AreCoordinates`), then under every `u x` the
value of the row `∑ ω g z g` (`rowValue`, `coordRows`) has the determinant of
`∑ ω g (u x g - 1)`, read in `L[X j]`. -/
lemma det_polyAction_rowValue {ι : Type} [Fintype ι] {gen : ι → G} {z : G → ι → O}
    (hz : AreCoordinates u gen z) (ω : G →₀ O) :
    (fun x : Y ↦ algebraMap (MvPolynomial J O) (MvPolynomial J L) (polyAction J (u x)
      (rowValue J gen (coordRows J ι (linearCombination O z ω)))).det) =
      fun x : Y ↦
        MvPolynomial.C (algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det) := by
  funext x
  have h_comb : Fintype.linearCombination O (fun i x ↦ u x (gen i) - 1)
      (linearCombination O z ω) x = linearCombination O (fun g : G ↦ u x g - 1) ω := by
    simp [hz, linearCombination, Finsupp.sum]
  rw [polyAction_rowValue_coordRows, h_comb]
  simp [det_apply']

/-- Let `u x` (`x : Y`) be matrix representations of the group `G` over `O`, with
`u x g - 1 = ∑ z g i (u x (gen i) - 1)` for all `g` and `x` (`AreCoordinates`). A row `r` over
`O[X j][G]` is tied (`tiedRows`) if `∑ r i (gen i - 1)` lies in `tieIdeal`, the left ideal of
`O[X j][G]` spanned by the elements that every `u x` kills, by `p I`, by the ties
`τ k - 1 - X j * (ε j)(φ k) * (φ k - 1)` for `k = (j, b)`, and by `I ρ₀`; here `p : O`, the `τ k`
and `φ k` are elements of `G`, the `ε j` are polynomials over `O`, and `I` is the augmentation
ideal. Let the `S`-module `𝒥` of families `Y → L[X j]` contain the traces under the `u x` of the
`p g` and of the ties times `g`, for `g : G` (part of `IsTraceIdeal`). If the rows of `R` are tied,
the value `∑ R j i (gen i - 1)` of row `j` is `b + m ρ₀`, with `b` in the left ideal spanned by the
`r` with the traces of all `r g` in `𝒥` (`traceLeftIdeal`) and `m` in the left ideal of the
`gen i - 1`. This is the hypothesis on rows of `exists_ribet_element_of_tied_rows`. -/
lemma exists_mulVec_eq_add_mul_of_mem_tiedRows {ι : Type} [Fintype ι] {gen : ι → G} {z : G → ι → O}
    (hz : AreCoordinates u gen z) (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ u x) p τ φ Prod.fst ε)
    {ρ₀ : (MvPolynomial J O)[G]} {R : Matrix ι ι (MvPolynomial J O)[G]}
    (hR : ∀ j : ι, R j ∈ tiedRows u gen p τ φ ε ρ₀) (j : ι) :
    ∃ b ∈ traceLeftIdeal u 𝒥, ∃ m ∈ span (MvPolynomial J O)[G]
          (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)),
        (R *ᵥ (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) j = b + m * ρ₀ := by
  let V : (ι → (MvPolynomial J O)[G]) →ₗ[(MvPolynomial J O)[G]] (MvPolynomial J O)[G] :=
    rowValue J gen
  have V_mem (w : ι → (MvPolynomial J O)[G]) :
      V w ∈ span (MvPolynomial J O)[G]
        (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) := by
    simp only [V, rowValue, Fintype.linearCombination_apply]
    exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have h_gen (g : G) : ∃ m ∈ span (MvPolynomial J O)[G]
      (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)),
      ∀ x : Y, polyAction J (u x) (.single g 1) = polyAction J (u x) m + 1 := by
    refine ⟨V (coordRows J ι (z g)), V_mem _, fun x ↦ ?_⟩
    rw [polyAction_rowValue_coordRows, hz g, polyAction_single, one_smul, map_sub, map_one,
      sub_add_cancel]
  obtain ⟨b, hb, m, hm, h_sum⟩ : ∃ b ∈ traceLeftIdeal u 𝒥,
      ∃ m ∈ augmentationIdeal (O := O) (G := G) J, b + m * ρ₀ = V (R j) := by
    obtain ⟨b, hb, _, ⟨m, hm, rfl⟩, h_sum⟩ := mem_sup.1 (tieIdeal_le u 𝒥 h𝒥 (mem_comap.1 (hR j)))
    exact ⟨b, hb, m, hm, h_sum⟩
  have h_row : (R *ᵥ (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) j = V (R j) := by
    simp [V, rowValue, mulVec, dotProduct, Fintype.linearCombination_apply]
  have h_aug (g : G) : polyChar J (1 : G →* O) (.single g 1) = 1 := by simp [polyChar_single]
  rw [h_row, ← h_sum]
  exact exists_mem_span_add_mul_eq_add_mul 𝒥 (fun x ↦ polyAction J (u x)) (polyChar J 1) h_aug _
    h_gen ρ₀ hb (RingHom.mem_ker.1 hm)

/-- If `S` holds the variables `X j`, the map from `O[X j]` to the constant families factors through
`S`. -/
lemma exists_ringHom_comp_eq_algebraMap (hS_X : ∀ j : J, (fun _ : Y ↦ MvPolynomial.X j) ∈ S) :
    ∃ κ : MvPolynomial J O →+* S, (algebraMap S (Y → MvPolynomial J L)).comp κ =
      algebraMap (MvPolynomial J O) (Y → MvPolynomial J L) := by
  let X' : J → S := fun j ↦ ⟨fun _ ↦ MvPolynomial.X j, hS_X j⟩
  refine ⟨(MvPolynomial.aeval X').toRingHom, MvPolynomial.ringHom_ext (fun c ↦ ?_) fun j ↦ ?_⟩
  · ext
    simp
  · ext
    simp [X']

/-- The characteristic polynomial of a group element `g` acting through `polyAction J ρ`, read over
`L[X j]`, has the constant coefficients given by the characteristic polynomial of `ρ g`. -/
lemma coeff_charpoly_map_polyAction_single (ρ : G →* Matrix σ σ O) (g : G) (k : ℕ) :
    ((polyAction J ρ (.single g 1)).map
        (algebraMap (MvPolynomial J O) (MvPolynomial J L))).charpoly.coeff k =
      MvPolynomial.C (algebraMap O L ((ρ g).charpoly.coeff k)) := by
  have h_map : (polyAction J ρ (.single g 1)).map
      (algebraMap (MvPolynomial J O) (MvPolynomial J L)) =
        (ρ g).map (MvPolynomial.C.comp (algebraMap O L)) := by
    ext1
    simp [polyAction_single]
  rw [h_map, charpoly_map, Polynomial.coeff_map, RingHom.comp_apply]

/-- The determinants of all combinations `∑ ω g (u x g - 1)`, as families of constant polynomials,
lie in `S` when `S` holds the variables and the coefficients of the characteristic polynomials of
the `u x g`. Here `z g` are coordinates of `u · g - 1` in the `u · (gen i) - 1`
(`AreCoordinates`). -/
lemma C_det_linearCombination_mem [Fintype J]
    (hS_X : ∀ j : J, (fun _ : Y ↦ MvPolynomial.X j) ∈ S)
    (hS_charpoly : ∀ (g : G) (k : ℕ),
      (fun x : Y ↦ MvPolynomial.C (algebraMap O L ((u x g).charpoly.coeff k))) ∈ S)
    {ι : Type} [Fintype ι] {gen : ι → G} {z : G → ι → O} (hz : AreCoordinates u gen z)
    (ω : G →₀ O) :
    (fun x : Y ↦ MvPolynomial.C
      (algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det)) ∈ S := by
  obtain ⟨κ, hκ⟩ : ∃ κ : MvPolynomial J O →+* S, (algebraMap S (Y → MvPolynomial J L)).comp κ =
      algebraMap (MvPolynomial J O) (Y → MvPolynomial J L) :=
    exists_ringHom_comp_eq_algebraMap hS_X
  rw [← det_polyAction_rowValue u hz]
  refine Selmer.det_mem_of_coeff_mem (fun x ↦ polyAction J (u x)) κ hκ (fun g k ↦ ?_) _
  simpa only [coeff_charpoly_map_polyAction_single] using hS_charpoly g k

/-- If `u x` is a block `ρ` plus characters `ξ e` with `ξ 0 = 1`, every combination
`∑ ω g (u x g - 1)` has determinant zero: its column at `ξ 0` is zero. -/
lemma det_linearCombination_sub_one_eq_zero {r : Type} {t : ℕ} [NeZero t]
    (blockEquiv : r ⊕ Fin t ≃ σ) {x : Y} {ρ : G → Matrix r r O} {ξ : Fin t → G →* O} (hξ₀ : ξ 0 = 1)
    (hu : ∀ g : G, u x g = reindex blockEquiv blockEquiv
      (fromBlocks (ρ g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (ω : G →₀ O) : (linearCombination O (fun g : G ↦ u x g - 1) ω).det = 0 := by
  have h_column (g : G) (i : σ) :
      u x g i (blockEquiv (inr 0)) = (1 : Matrix σ σ O) i (blockEquiv (inr 0)) := by
    obtain ⟨i | i, rfl⟩ := blockEquiv.surjective i
    · simp [hu, one_apply]
    · simp +contextual [hu, hξ₀, one_apply, diagonal_apply]
  refine det_eq_zero_of_column_eq_zero (blockEquiv (inr 0)) fun i ↦ ?_
  simp [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply, h_column]

/-- The gluing. Let `u x` (`x : Y`) be matrix representations of the group `G` over `O`, with
`u x g - 1 = ∑ z g i (u x (gen i) - 1)` for all `g` and `x` (`AreCoordinates`). On `𝓧`, `u x` is,
after reindexing along `blockEquiv`, the block `ρ x` plus the characters `ξ e`, with `ξ 0 = 1`.
Further let `S` be an algebra of families `Y → L[X j]`, where `L[X j]` is `MvPolynomial J L`, and
`𝒥` an `S`-module of such families; `S` contains the `X j` and the coefficients of the
characteristic polynomials of the `u x g`, and `𝒥` the traces under the `u x` of the `p g` and of
the ties (see below) times `g` (`IsTraceIdeal`). Representations act on `O[X j][G]` through
`polyAction` and characters through `polyChar`. Let `k` be `1` on the characters and `0` on the
blocks, and let `q₀` be `μ₀` on `ξ 0` and `0` on the other characters. Let `B₀` and the `M i`
(`i : κ`) be matrices of tied rows for `ρ₀ = n + (1 - n) (a - 1)` with `n = c₁ (γ - 1)`
(`tiedNormaliser`), and `wt i` weights. Then one `f : S` multiplies the determinants of all
combinations `∑ ω g (u x g - 1)` into `𝒥`, and its value at `x ∈ 𝓧` is
`∑ wt i μ₀ det (B₀ on the block) ∏ det (M i on ξ e)`. A row `r` over `O[X j][G]` is tied
(`tiedRows`) if `∑ r i (gen i - 1)` lies in `tieIdeal`, the left ideal of `O[X j][G]` spanned by the
elements that every `u x` kills, by `p I`, by the ties `τ l - 1 - X j * (ε j)(φ l) * (φ l - 1)` for
`l = (j, b)`, and by `I ρ₀`; here `p : O`, the `τ l` and `φ l` are elements of `G`, the `ε j` are
polynomials over `O`, and `I` is the augmentation ideal. -/
lemma exists_traceIdeal_multiplier_eq_sum_det [Fintype J] {r : Type} [Fintype r] [DecidableEq r]
    {t : ℕ} [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ) {𝓧 : Set Y} (ρ : 𝓧 → G →* Matrix r r O)
    {ξ : Fin t → G →* O} (hξ₀ : ξ 0 = 1)
    (hu_block : ∀ (x : 𝓧) (g : G),
      u x g = reindex blockEquiv blockEquiv
        (fromBlocks (ρ x g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ u x) p τ φ Prod.fst ε)
    {ι : Type} [Fintype ι] [DecidableEq ι] {gen : ι → G} {z : G → ι → O}
    (hz : AreCoordinates u gen z)
    {γ a : G} {c₁ : O} {k q₀ : (MvPolynomial J O)[G]} (hkξ : ∀ e : Fin t, polyChar J (ξ e) k = 1)
    (hkρ : ∀ x : 𝓧, polyAction J (ρ x) k = 0) {μ₀ : MvPolynomial J O}
    (hq₀ : ∀ e : Fin t, polyChar J (ξ e) q₀ = if e = 0 then μ₀ else 0)
    (B₀ : Matrix ι ι (MvPolynomial J O)[G])
    (hB₀ : ∀ i : ι, B₀ i ∈ tiedRows u gen p τ φ ε (tiedNormaliser J γ a c₁))
    {κ : Type} [Fintype κ] (wt : κ → MvPolynomial J O) (M : κ → Matrix ι ι (MvPolynomial J O)[G])
    (hM : ∀ (i : κ) (j : ι), M i j ∈ tiedRows u gen p τ φ ε (tiedNormaliser J γ a c₁)) :
    ∃ f : S,
      (∀ ω : G →₀ O, (f : Y → MvPolynomial J L) * (fun x : Y ↦ MvPolynomial.C
        (algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det)) ∈ 𝒥) ∧
      ∀ x : 𝓧, (f : Y → MvPolynomial J L) x =
        algebraMap (MvPolynomial J O) (MvPolynomial J L) (∑ i : κ, wt i * (μ₀ *
          (Matrix.comp ι ι r r (MvPolynomial J O) (B₀.map (polyAction J (ρ x)))).det *
            ∏ e : Fin t, ((M i).map (polyChar J (ξ e))).det)) := by
  let Λ : Type := MvPolynomial J O
  let χ (x : Y) : Λ[G] →ₐ[Λ] Matrix σ σ Λ := polyAction J (u x)
  let ψ (x : 𝓧) : Λ[G] →ₐ[Λ] Matrix r r Λ := polyAction J (ρ x)
  let η (e : Fin t) : Λ[G] →ₐ[Λ] Λ := polyChar J (ξ e)
  let N : Submodule Λ[G] (ι → Λ[G]) := tiedRows u gen p τ φ ε (tiedNormaliser J γ a c₁)
  let gen_sub_one : ι → Λ[G] := MonoidAlgebra.of Λ G ∘ gen - 1
  -- Ribet's element for `(1 - k) • B₀ + k • M i`, with `ρ₁ = k q₀`; `κS` lifts `Λ` to `S`.
  obtain ⟨κS, hκS⟩ : ∃ κS : Λ →+* S, (algebraMap S (Y → MvPolynomial J L)).comp κS =
      algebraMap Λ (Y → MvPolynomial J L) :=
    exists_ringHom_comp_eq_algebraMap h𝒥.X_mem
  have hχ_coeff (g : G) (n : ℕ) :
      (fun x ↦ ((χ x (.single g 1)).map (algebraMap Λ (MvPolynomial J L))).charpoly.coeff n) ∈
        S := by
    simpa only [χ, Λ, coeff_charpoly_map_polyAction_single] using h𝒥.charpoly_coeff_mem g n
  have hη₀ : η 0 (tiedNormaliser J γ a c₁) = 0 := by
    simp [η, Λ, tiedNormaliser, polyChar_single, hξ₀, AlgHom.map_smul_of_tower]
  have hψ₁ (x : 𝓧) : ψ x (k * q₀) = 0 := by simp [ψ, hkρ]
  have hη₁ (e : Fin t) : η e (k * q₀) = if e = 0 then μ₀ else 0 := by simp [η, hkξ, hq₀]
  have h_tied (i : κ) (j : ι) : ((1 - k) • B₀ + k • M i) j ∈ N :=
    add_mem (N.smul_mem _ (hB₀ j)) (N.smul_mem _ (hM i j))
  have exists_f (i : κ) : ∃ f : S,
      (∀ w ∈ span Λ[G] (Set.range gen_sub_one),
        f.1 * (fun x ↦ algebraMap Λ (MvPolynomial J L) (χ x w).det) ∈ 𝒥) ∧
      ∀ x : 𝓧, f.1 x = algebraMap Λ (MvPolynomial J L) (μ₀ *
        (Matrix.comp ι ι r r Λ (((1 - k) • B₀ + k • M i).map (ψ x))).det *
        ∏ e, (((1 - k) • B₀ + k • M i).map (η e)).det) :=
    Selmer.exists_ribet_element_of_tied_rows blockEquiv χ κS hκS hχ_coeff 𝒥 gen_sub_one
      (tiedNormaliser J γ a c₁) (k * q₀) ((1 - k) • B₀ + k • M i)
      (exists_mulVec_eq_add_mul_of_mem_tiedRows u 𝒥 hz h𝒥 (h_tied i))
      ψ η (fun x ↦ polyAction_eq_reindex u blockEquiv (hu_block x)) hψ₁ hη₁ hη₀
  choose f hf_mem hf_eq using exists_f
  refine ⟨∑ i, κS (wt i) * f i, fun ω ↦ ?_, fun x ↦ ?_⟩
  · -- `det (∑ ω g (u x g - 1))` is the determinant of `w` acting through `u x`.
    let w : Λ[G] := rowValue J gen (coordRows J ι (linearCombination O z ω))
    have hw : w ∈ span Λ[G] (Set.range gen_sub_one) := by
      simp only [w, rowValue, Fintype.linearCombination_apply]
      exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩)
    rw [← det_polyAction_rowValue u hz, ← smul_eq_mul, ← Subalgebra.smul_def, Finset.sum_smul]
    refine sum_mem fun i _ ↦ ?_
    rw [mul_smul, Subalgebra.smul_def (f i), smul_eq_mul]
    exact 𝒥.smul_mem _ (hf_mem i w hw)
  · -- On `𝓧`, `(1 - k) • B₀ + k • M i` is `B₀` on the block and `M i` on the characters.
    have hκS_apply (c : Λ) : (κS c).1 x = algebraMap Λ (MvPolynomial J L) c :=
      congrFun (RingHom.congr_fun hκS c) x
    have h_block (i : κ) : ((1 - k) • B₀ + k • M i).map (ψ x) = B₀.map (ψ x) := by
      ext1
      simp [ψ, hkρ]
    have h_chars (i : κ) (e : Fin t) : ((1 - k) • B₀ + k • M i).map (η e) = (M i).map (η e) := by
      ext1
      simp [η, hkξ]
    simp [hf_eq, hκS_apply, h_block, h_chars, map_sum, ψ, η, Λ]

/-- The projector to the characters: if every block `ρ x` has an element `γ x` acting by a scalar
`y x` with `y x - 1` a unit, on which every character is `1`, then some element of `O[X j][G]` is
`1` on every character and `0` on every block. -/
lemma exists_character_projector [Fintype J] {r : Type} [Fintype r] [DecidableEq r] {t : ℕ}
    {𝓧 : Type} [Fintype 𝓧] (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O} {γ : 𝓧 → G} {y : 𝓧 → O}
    (hργ : ∀ x : 𝓧, ρ x (γ x) = y x • 1) (hy_unit : ∀ x : 𝓧, IsUnit (y x - 1))
    (hξγ : ∀ (x : 𝓧) (e : Fin t), ξ e (γ x) = 1) :
    ∃ k : (MvPolynomial J O)[G],
      (∀ e : Fin t, polyChar J (ξ e) k = 1) ∧
      ∀ x : 𝓧, polyAction J (ρ x) k = 0 := by
  refine exists_forall_eq_one_and_forall_eq_zero (fun e ↦ polyChar J (ξ e))
    (fun x ↦ polyAction J (ρ x))
    fun x ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : O, c * (y x - 1) = 1 := (hy_unit x).exists_left_inv
  let w : (MvPolynomial J O)[G] :=
    (MvPolynomial.C (y x) : MvPolynomial J O) • 1 - MonoidAlgebra.single (γ x) 1
  have h_char (e : Fin t) : polyChar J (ξ e) w = MvPolynomial.C (y x - 1) := by
    simp [w, polyChar_single, hξγ]
  have h_block : polyAction J (ρ x) w = 0 := by
    simp [w, polyAction_single, hργ, smul_one_eq_diagonal]
  refine ⟨(MvPolynomial.C c : MvPolynomial J O) • w, fun e ↦ ?_, ?_⟩
  · rw [map_smul, h_char, smul_eq_mul, ← map_mul, hc, map_one]
  · rw [map_smul, h_block, smul_zero]

/-- Finitely many generators. Let `u x` (`x : Y`) be finitely many matrix representations of `G`
over the discrete valuation ring `O`. There are a finite `s₀ ⊆ G` and vectors `z g` over `O` with
`u x g - 1 = ∑ z g i (u x (gen i) - 1)` for all `g` and `x` (`AreCoordinates`), where `gen` lists
the `δ w`, the members of `s₀` and those of `s` (`ribetGenerators`). -/
lemma exists_areCoordinates_ribetGenerators (u : Y → G →* Matrix σ σ O) [DVR O] [Fintype Y]
    [Fintype W] (δ : W → G) (s : Finset G) :
    ∃ (s₀ : Finset G) (z : G → W ⊕ s₀ ⊕ s → O),
      AreCoordinates u (ribetGenerators δ s₀ s) z := by
  classical
  let v (g : G) : Y → Matrix σ σ O := fun x ↦ u x g - 1
  have h_compact : IsCompactElement (⨆ g : G, O ∙ v g) := (fg_iff_compact _).1 .of_finite
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Finset G, ⨆ g : G, (O ∙ v g) ≤ ⨆ g ∈ s₀, (O ∙ v g) :=
    h_compact.exists_finset_of_le_iSup _ le_rfl
  let gen : W ⊕ s₀ ⊕ s → G := ribetGenerators δ s₀ s
  let T : (W ⊕ s₀ ⊕ s → O) →ₗ[O] Y → Matrix σ σ O :=
    Fintype.linearCombination O fun i ↦ v (gen i)
  have h_range : ⨆ g ∈ s₀, (O ∙ v g) ≤ T.range := by
    refine iSup₂_le fun g hg ↦ ?_
    rw [span_singleton_le_iff_mem]
    exact ⟨Pi.single (inr (inl ⟨g, hg⟩)) 1, by simp [T, gen]⟩
  have exists_z (g : G) : ∃ m : W ⊕ s₀ ⊕ s → O, T m = v g :=
    LinearMap.mem_range.1 (hs₀.trans h_range (mem_iSup_of_mem g (mem_span_singleton_self _)))
  choose z hz using exists_z
  exact ⟨s₀, z, hz⟩

section CharacterRows

variable {u : Y → G →* Matrix σ σ O}
variable [DVR O] [Fintype J] [LinearOrder J] [DecidableEq G] {t : ℕ} {ξ : Fin t → G →* O}
  [Fintype W] [DecidableEq W] {δ : W → G} {o : W → O[X]} {s₀ s : Finset G} {γ a : G} {c₁ C : O}
  {ty : J →o Fin t} {b : Fin t → ℕ∞}

/-- Let `R` be a system of matrices for the characters `ξ e`, `e : Fin t` (`CharacterRows`). For
each `e` it has `R.count e` matrices `R.charMatrix e j` over `O[X j]` and weights `R.coeff e j` with
`∑ j, R.coeff e j det (R.charMatrix e j) = R.detSum e`. For each choice `i` of one index `i e` for
every `e`, it has a matrix `R.tiedMatrix i` over `O[X j][G]` whose determinant on `ξ e` is
`c₀ det (R.charMatrix e (i e))`, where `c₀ = (∏ o v (1)) C ^ #s`. Then the products over `e` of the
determinants of `R.tiedMatrix i` on the `ξ e`, summed with the weights `∏ R.coeff e (i e)`, give
`c₀ ^ t ∏ R.detSum e`. -/
lemma CharacterRows.sum_prod_coeff_mul_prod_det_tiedMatrix
    (R : CharacterRows u ξ δ o s₀ s γ a c₁ C p τ φ ε ty b) :
    ∑ i : ∀ e : Fin t, Fin (R.count e),
        (∏ e : Fin t, R.coeff e (i e)) * ∏ e : Fin t,
          ((R.tiedMatrix i).map (polyChar J (ξ e))).det =
      MvPolynomial.C ((∏ v : W, (o v).eval 1) * C ^ #s) ^ t * ∏ e : Fin t, R.detSum e := by
  set c₀ : MvPolynomial J O := MvPolynomial.C ((∏ v : W, (o v).eval 1) * C ^ #s) with hc₀
  calc _ = ∑ i : ∀ e : Fin t, Fin (R.count e), c₀ ^ t * ∏ e,
         R.coeff e (i e) * (R.charMatrix e (i e)).det := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [R.det_map, ← hc₀, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
        ring
    _ = c₀ ^ t * ∏ e, ∑ j, R.coeff e j * (R.charMatrix e j).det := by
      rw [Fintype.prod_sum, Finset.mul_sum]
    _ = c₀ ^ t * ∏ e, R.detSum e := by simp only [R.sum_det]

/-- Let `O` be a discrete valuation ring with additive valuation `v = addVal O`, and let `R` be a
system of matrices for the characters `ξ e`, `e : Fin t` (`CharacterRows`). It has polynomials
`R.multiplier e` in the variables `X j` with
`R.detSum e + R.correction e = R.multiplier e * ∏ j with ty j = e, X j`, and the constant term of
`R.multiplier e` has valuation at most `b e + (#{j | ty j = e} + #s) v(C)`. As the sets
`{j | ty j = e}` partition `J`, the constant term of `∏ R.multiplier e` has valuation at most
`∑ b e + (#J + t #s) v(C)`. -/
lemma CharacterRows.addVal_constantCoeff_prod_le
    (R : CharacterRows u ξ δ o s₀ s γ a c₁ C p τ φ ε ty b) :
    addVal O (constantCoeff (∏ e : Fin t, R.multiplier e)) ≤
      ∑ e : Fin t, b e + (Fintype.card J + t * #s) * addVal O C := by
  have h_card : ∑ e : Fin t, (#{j : J | ty j = e} : ℕ∞) = Fintype.card J := by
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _, card_univ]
  rw [map_prod, addVal_prod]
  calc _ ≤ ∑ e : Fin t, (b e + (#{j : J | ty j = e} + #s) * addVal O C) :=
        sum_le_sum fun e _ ↦ R.addVal_constantCoeff_le e
    _ = _ := by simp [sum_add_distrib, ← sum_mul, h_card]

end CharacterRows
end Steps

section Lemma

variable {O L Y G J σ W : Type} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  [Group G] (u : Y → G →* Matrix σ σ O) {S : Subalgebra O (Y → MvPolynomial J L)}
  (𝒥 : Submodule S (Y → MvPolynomial J L))

/-- Membership in `ribetCocyclesIn`: `c` is a cocycle for `ρ`, and it obeys every linear relation
among the families `u · g - 1`. -/
lemma mem_ribetCocyclesIn_iff {r : Type} [Fintype r] [DecidableEq r] {ρ : G →* Matrix r r O}
    {B : Type} [AddCommGroup B] [Module O B] {c : G → r → B} :
    c ∈ ribetCocyclesIn u ρ B ↔ c ∈ obeying (cocycleRelations ρ) B ∧ ∀ θ : G →₀ O,
      linearCombination O (fun (g : G) (x : Y) ↦ u x g - 1) θ = 0 → linearCombination O c θ = 0 :=
  Iff.rfl

/-- Let `u x` (`x : Y`) be matrix representations of the group `G` over `O`, and let `f` be an
injective linear map of coefficient modules. Then `c` is a cocycle for `ρ` with `∑ θ g • c g = 0`
whenever `∑ θ g • (u x g - 1) = 0` for all `x` (`ribetCocyclesIn`) if and only if `f ∘ c` is one. -/
lemma comp_mem_ribetCocyclesIn_iff (u : Y → G →* Matrix σ σ O) {r : Type} [Fintype r]
    [DecidableEq r]
    {ρ : G →* Matrix r r O} {B B' : Type} [AddCommGroup B] [Module O B] [AddCommGroup B']
    [Module O B'] {f : B →ₗ[O] B'} (hf : Function.Injective f) {c : G → r → B} :
    (fun (g : G) (i : r) ↦ f (c g i)) ∈ ribetCocyclesIn u ρ B' ↔ c ∈ ribetCocyclesIn u ρ B := by
  have h_lc (θ : G →₀ O) : linearCombination O (fun (g : G) (i : r) ↦ f (c g i)) θ =
      fun i : r ↦ f (linearCombination O c θ i) := by
    ext i
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  have h_obey : (fun (g : G) (i : r) ↦ f (c g i)) ∈ obeying (cocycleRelations ρ) B' ↔
      c ∈ obeying (cocycleRelations ρ) B := by
    rw [comp_mem_obeying_iff, mem_obeying]
    refine forall₂_congr fun F _ ↦ ?_
    simp only [map_eq_zero_iff f hf, funext_iff, Pi.zero_apply]
  rw [mem_ribetCocyclesIn_iff, mem_ribetCocyclesIn_iff]
  refine and_congr h_obey (forall₂_congr fun θ _ ↦ ?_)
  simp only [h_lc, map_eq_zero_iff f hf, funext_iff, Pi.zero_apply]

/-- Let `u x` be a finite family of representations of `G` over a discrete valuation ring `O` with
fraction field `K`. The cocycles of `ρ` with values in `K/O` that obey the linear relations among
the families `(u x g - 1)_x` are torsion: by the coordinates of
`exists_areCoordinates_ribetGenerators` the values of a member are combinations of finitely many of
them, and each element of `K/O` has a nonzero denominator. -/
lemma exists_smul_eq_zero_of_mem_ribetCocyclesIn [DVR O] [Fintype Y] {r : Type} [Fintype r]
    [DecidableEq r] {ρ : G →* Matrix r r O} {c : G → r → DivisibleQuot O}
    (hc : c ∈ ribetCocyclesIn u ρ (DivisibleQuot O)) : ∃ a : O, a ≠ 0 ∧ a • c = 0 := by
  classical
  obtain ⟨-, h_rel⟩ := (mem_ribetCocyclesIn_iff u).1 hc
  have exists_d (y : DivisibleQuot O) : ∃ d : O, d ≠ 0 ∧ d • y = 0 :=
    exists_smul_eq_zero_divisibleQuot y
  choose d hd_ne hd using exists_d
  obtain ⟨s₀, z, hz⟩ : ∃ (s₀ : Finset G) (z : G → Empty ⊕ s₀ ⊕ (∅ : Finset G) → O),
      AreCoordinates u (ribetGenerators Empty.elim s₀ ∅) z :=
        exists_areCoordinates_ribetGenerators u Empty.elim ∅
  let gen : Empty ⊕ s₀ ⊕ (∅ : Finset G) → G := ribetGenerators Empty.elim s₀ ∅
  -- The value at `g` is the combination of the values at the generators with coefficients `z g`.
  have h_val (g : G) : c g = ∑ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), z g i • c (gen i) := by
    have h_g : Fintype.linearCombination O (fun i x ↦ u x (gen i) - 1) (z g) =
        fun x ↦ u x g - 1 := hz g
    have hθ : linearCombination O (fun (g : G) (x : Y) ↦ u x g - 1)
        (Finsupp.single g 1 - ∑ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), Finsupp.single (gen i) (z g i)) =
          0 := by
      simp [map_sub, map_sum, Finsupp.linearCombination_single, ← h_g,
        Fintype.linearCombination_apply]
    simpa [map_sub, map_sum, Finsupp.linearCombination_single, sub_eq_zero] using h_rel _ hθ
  let a : O := ∏ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), ∏ k : r, d (c (gen i) k)
  refine ⟨a, by simp [a, Finset.prod_ne_zero_iff, hd_ne], funext fun g ↦ funext fun k ↦ ?_⟩
  simp only [Pi.smul_apply, Pi.zero_apply, h_val g, Finset.sum_apply, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  obtain ⟨e, he⟩ : ∃ e : O, a = d (c (gen i) k) * e :=
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i ↦ ∏ k : r, d (c (gen i) k)) (Finset.mem_univ i))
  rw [smul_comm, he, mul_comm, mul_smul, hd, smul_zero, smul_zero]

/-- From coefficients modulo powers of `p` to coefficients in `K/O = Frac(O) / O`. Let `u x` be a
finite family of representations of `G` over `O`. Consider the cocycles `c` of `ρ` that vanish on
`T` and at `γ` and have `∑ θ g • c g = 0` whenever `∑ θ g • (u x g - 1) = 0` for all `x`. If for
every `M` those modulo `p ^ M` have length at most `b`, where `p ≠ 0` is not a unit, so have those
with values in `K/O`: division by `a = p ^ (b + 1)` maps the cocycles modulo `a` onto the
`a`-torsion, and as `v(a) > b` this torsion is everything. -/
lemma length_ribetCocyclesVanishingOn_divisibleQuot_le [DVR O] [Fintype Y] {r : Type}
    [Fintype r] [DecidableEq r] (ρ : G →* Matrix r r O) (T : Set G) (γ : G) {p : O} (hp : p ≠ 0)
    (hp_unit : ¬IsUnit p) {b : ℕ}
    (h_length_pow : ∀ M : ℕ, length O (ribetCocyclesVanishingOn u ρ (QuotSpan (p ^ M)) T γ) ≤ b) :
    length O (ribetCocyclesVanishingOn u ρ (DivisibleQuot O) T γ) ≤ b := by
  set V : Submodule O (G → r → DivisibleQuot O) :=
    ribetCocyclesVanishingOn u ρ (DivisibleQuot O) T γ
  let a : O := p ^ (b + 1)
  have ha : a ≠ 0 := pow_ne_zero _ hp
  let E : (G → r → QuotSpan a) →ₗ[O] G → r → DivisibleQuot O :=
    ((divQuot a).compLeft r).compLeft G
  -- The `a`-torsion of `V` is the image of the cocycles modulo `a`.
  have h_le : (torsionBy O V a).map V.subtype ≤
      (ribetCocyclesVanishingOn u ρ (QuotSpan a) T γ).map E := by
    rintro _ ⟨⟨c, hcV⟩, hc_tors, rfl⟩
    have hc_smul : a • c = 0 := congrArg Subtype.val ((mem_torsionBy_iff a _).1 hc_tors)
    have exists_c' (g : G) (i : r) : ∃ x : QuotSpan a, divQuot a x = c g i :=
      exists_divQuot_eq ha (congrFun₂ hc_smul g i)
    choose c' hc' using exists_c'
    have h_zero {g : G} (hg : c g = 0) : c' g = 0 :=
      funext fun i ↦ divQuot_injective ha (by simp [hc', hg])
    obtain ⟨h_obey, h_T, h_γ⟩ : c ∈ ribetCocyclesIn u ρ (DivisibleQuot O) ∧
        (∀ g ∈ T, c g = 0) ∧ c γ = 0 := (mem_ribetCocyclesVanishingOn u).1 hcV
    refine ⟨c', (mem_ribetCocyclesVanishingOn u).2
      ⟨?_, fun g hg ↦ h_zero (h_T g hg), h_zero h_γ⟩, funext₂ hc'⟩
    rw [← comp_mem_ribetCocyclesIn_iff u (divQuot_injective ha)]
    simpa only [hc'] using h_obey
  have h_length : length O (torsionBy O V a) ≤ b := by
    rw [(Submodule.equivMapOfInjective V.subtype V.injective_subtype _).length_eq]
    exact (length_le_of_le_map E _ h_le).trans (h_length_pow (b + 1))
  -- Every member of `V` is torsion and `v(a) ≥ b + 1`, so the `a`-torsion is all of `V`.
  have h_torsion : ∀ w : V, ∃ a' : O, a' ≠ 0 ∧ a' • w = 0 := by
    rintro ⟨c, hcV⟩
    obtain ⟨h_obey, -⟩ := (mem_ribetCocyclesVanishingOn u).1 hcV
    obtain ⟨a', ha', ha'c⟩ : ∃ a' : O, a' ≠ 0 ∧ a' • c = 0 :=
      exists_smul_eq_zero_of_mem_ribetCocyclesIn u h_obey
    exact ⟨a', ha', Subtype.ext ha'c⟩
  have h_va : (b : ℕ∞) + 1 ≤ addVal O a := by
    have h_one : 1 ≤ addVal O p := Order.one_le_iff_ne_zero.2 fun h_val_zero ↦
      hp_unit (addVal_eq_zero_iff.1 h_val_zero)
    calc (b : ℕ∞) + 1 = (b + 1 : ℕ) • (1 : ℕ∞) := by simp
      _ ≤ (b + 1 : ℕ) • addVal O p := nsmul_le_nsmul_right h_one _
      _ = addVal O a := (addVal_pow p (b + 1)).symm
  have h_top : torsionBy O V a = ⊤ := by
    by_contra h_ne
    have h_cast : ((b + 1 : ℕ) : ℕ∞) ≤ b := by
      rw [Nat.cast_succ]
      exact h_va.trans ((addVal_le_length_torsionBy h_torsion h_ne).trans h_length)
    exact absurd (Nat.cast_le.1 h_cast) (by omega)
  rw [← length_top, ← h_top]
  exact h_length

/-- Ribet's lemma to first order, for any group and any discrete valuation ring. Let `u x` (`x : Y`)
be a finite family of matrix representations of `G` over `O` and `L` an `O`-algebra; let `S` be an
algebra of families `Y → L[X j]`, where `L[X j]` is `MvPolynomial J L`, and `𝒥` an `S`-module of
such families. (1) On `𝓧`, `u x` is, after reindexing along `blockEquiv`, a block `ρ x` plus
characters `ξ e` with `ξ 0 = 1`, and `ρ π` spans all matrices. (2) An element `γ x` acts on the
block by a scalar `y x` with `y x - 1` a unit, and trivially on the characters. (3) For `p ≠ 0` in
`O`, elements `τ k`, `φ k` of `G` (`k : J × Bool`) and polynomials `ε j` over `O`, `S` contains the
`X j` and the coefficients of the characteristic polynomials of the `u x g`, and `𝒥` contains the
families over `x` of the traces under `u x` of `p g` and of
`(τ k - 1 - X j * (φ k - 1) * (ε j)(φ k)) * g` for `g : G` and `k = (j, b)` (`IsTraceIdeal`); `ε j`
is `1` modulo `p` at the `ξ e (φ k)`. (4) For an element `a` of `G` and each `e`, the product of the
`ξ e a - ξ k a` over `k ≠ e` divides `C`; each `j` has a type `ty j`, monotone in `j`. (5) The
cocycles `c` of `ρ π` with values in `Frac(O) / O` that have `∑ θ g • c g = 0` whenever
`∑ θ g • (u x g - 1) = 0` for all `x` and vanish at the `τ k` and at `γ π` form a module of length
at most `b₀`. (6) The `δ v` are trivial on the characters and `o v * (X - 1)` kills every
`u x (δ v)`. (7) Every module `Z` of character cocycles for `ξ e` satisfies `HasTriangleCost` along
the `j` of type `e`, and a member of `Z` that vanishes on the finite set `s ⊆ G` is zero
(`IsDetectedBy`). Then the determinants of all combinations `∑ ω g (u x g - 1)` lie in `S` and
vanish on `𝓧`, one `f : S` multiplies them into `𝒥`, `f` has on `𝓧` no monomial properly dividing
`∏ X j`, and the coefficient of `∏ X j` in `f π` comes from some `c : O` of valuation at most
`b₀ + ∑ b e + t (∑ val (o v (1)) + 2 #s val C) + (#J + 1) val C`, with `val = addVal O` and `t` the
number of characters. A character cocycle for `ξ e` is a cocycle `c : G → O / p` for `ξ e` that has
`∑ θ g • c g = 0` whenever `∑ θ g • (u x g - 1) = 0` for all `x`, vanishes at the `δ v`, and, if it
vanishes at `γ π`, has `(ξ e g - 1) • c a = 0` for all `g`. `HasTriangleCost` asks for a set `A ⊆ G`
such that, with `Z₀` the part of `Z` vanishing on `A`: for `j` of type `e` and `c ∈ Z₀`, `C` kills
`c (τ (j, true)) - c (τ (j, false))` as soon as `c (τ (i, true)) = c (τ (i, false))` for all `i < j`
and `c (φ (i, true)) = c (φ (i, false))` for the `i < j` of type `e`; and the length of `Z / Z₀`
plus the length of `Z₁` modulo its `C`-torsion is at most `b e`, for every submodule `Z₁ ≤ Z₀` whose
members vanish at all `τ k` and have `c (φ (j, true)) = c (φ (j, false))` for `j` of type `e`. -/
lemma exists_isCommonRibetElement_addVal_le (u : Y → G →* Matrix σ σ O)
    {S : Subalgebra O (Y → MvPolynomial J L)} (𝒥 : Submodule S (Y → MvPolynomial J L))
    [DVR O] [Fintype Y] [Fintype J] [LinearOrder J] {r : Type}
    [Fintype r] [DecidableEq r] {t : ℕ} [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ)
    -- (1) on `𝓧`, `u x` is the block `ρ x` plus the characters `ξ e`
    {𝓧 : Set Y} (π : 𝓧) (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O} (hξ₀ : ξ 0 = 1)
    (hu_block : ∀ (x : 𝓧) (g : G),
      u x g = reindex blockEquiv blockEquiv
        (fromBlocks (ρ x g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (hρ_span : span O (Set.range (ρ π)) = ⊤)
    -- (2) `γ x` is a scalar `y x` on the block, `y x - 1` a unit, and trivial on the characters
    {γ : 𝓧 → G} {y : 𝓧 → O} (hργ : ∀ x : 𝓧, ρ x (γ x) = y x • 1)
    (hy_unit : ∀ x : 𝓧, IsUnit (y x - 1)) (hξγ : ∀ (x : 𝓧) (e : Fin t), ξ e (γ x) = 1)
    -- (3) two relations in `𝒥` for each `j : J`, indexed by `(j, true)` and `(j, false)`, whose
    -- factors `ε` are `1` modulo `p` on the characters
    {p : O} {τ φ : J × Bool → G} {ε : J → O[X]} (hp : p ≠ 0)
    (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ u x) p τ φ Prod.fst ε)
    (hε : ∀ (e : Fin t) (k : J × Bool), p ∣ (ε k.1).eval (ξ e (φ k)) - 1)
    -- (4) `a` separates the characters up to `C`; `ty j` is the character that `j` belongs to
    (a : G) {C : O}
    (hC_dvd : ∀ e : Fin t, ∏ k ∈ ({e}ᶜ : Finset (Fin t)), (ξ e a - ξ k a) ∣ C) (ty : J →o Fin t)
    -- (5) the bound `b₀` for cocycles of the block with values in `K/O` that vanish at the `τ k`
    -- and at `γ π`
    {b₀ : ℕ}
    (hb₀ : length O (ribetCocyclesVanishingOn u (ρ π) (DivisibleQuot O) (Set.range τ) (γ π)) ≤ b₀)
    -- (6) elements `δ v`, trivial on the characters, with `u x (δ v)` killed by `o v * (X - 1)`
    [Fintype W] {δ : W → G} {o : W → O[X]} (hξδ : ∀ (v : W) (e : Fin t), ξ e (δ v) = 1)
    (hδ_poly : ∀ (v : W) (x : Y), aeval (u x (δ v)) (o v * (X - 1)) = 0)
    -- (7) a module `Z` of cocycles of `ξ e` modulo `p` costs at most `b e` and is detected by `s`
    {s : Finset G} {b : Fin t → ℕ∞}
    (hb : ∀ (e : Fin t) (Z : Submodule O (G → Unit → QuotSpan p)),
      (∀ c ∈ Z, IsCharacterCocycle u (ξ e) δ (γ π) a c) →
      HasTriangleCost Z (fun j : J ↦ τ (j, true)) (fun j : J ↦ τ (j, false))
          (fun j : J ↦ φ (j, true)) (fun j : J ↦ φ (j, false)) {j : J | ty j = e} C (b e) ∧
        IsDetectedBy Z s) :
    ∃ c : O,
      -- (a) `c` is the coefficient of `∏ X j` at `π` in one Ribet element for every `ω`
      IsCommonRibetElement 𝒥
        (fun (ω : G →₀ O) (x : Y) ↦
          algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det)
        π (algebraMap O L c) ∧
      -- (b) its valuation is at most the bounds `b₀`, `b e` plus the loss
      addVal O c ≤ b₀ + (∑ e : Fin t, b e +
        t * (∑ v : W, addVal O (eval 1 (o v)) + 2 * #s * addVal O C) +
        (Fintype.card J + 1) * addVal O C) := by
  classical
  -- Over `O[X j][G]`: a matrix `B₀` of tied rows whose determinant on the summand `ρ π` has bounded
  -- valuation at `X j = 0`, and matrices of tied rows giving a multiple of `∏ X j` on the
  -- characters, up to monomials that are not read, are glued by a projector `k` into one element.
  obtain ⟨k, hkξ, hkρ⟩ : ∃ k : (MvPolynomial J O)[G], (∀ e : Fin t, polyChar J (ξ e) k = 1) ∧
      ∀ x : 𝓧, polyAction J (ρ x) k = 0 := exists_character_projector ρ hργ hy_unit hξγ
  -- Elements `q e` that are `C` on the character `ξ e` and `0` on the other characters.
  have exists_q (e : Fin t) : ∃ q : (MvPolynomial J O)[G],
      ∀ e' : Fin t, polyChar J (ξ e') q = if e' = e then .C C else 0 := by
    refine exists_apply_eq_ite_of_prod_dvd (fun e' ↦ polyChar J (ξ e')) (.single a 1) ?_
    simpa [polyChar_single] using map_dvd (MvPolynomial.C (σ := J)) (hC_dvd e)
  choose q hq using exists_q
  -- Generators: the `δ v`, a finite `s₀` whose `u · g - 1` span all the others, and `s`.
  obtain ⟨s₀, z, hz⟩ : ∃ (s₀ : Finset G) (z : G → W ⊕ s₀ ⊕ s → O),
      AreCoordinates u (ribetGenerators δ s₀ s) z := exists_areCoordinates_ribetGenerators u δ s
  -- With `c₁ = 1 / (y π - 1)`, the element `c₁ (γ π - 1)` of `tiedNormaliser` is `1` on `ρ π`.
  obtain ⟨c₁, hc₁⟩ : ∃ c : O, c * (y π - 1) = 1 := (hy_unit π).exists_left_inv
  -- The block: tied rows `B₀` whose determinant on `ρ π`, at `X j = 0`, has valuation at most `b₀`.
  obtain ⟨B₀, hB₀, hB₀_val⟩ : ∃ B₀ : Matrix (W ⊕ s₀ ⊕ s) (W ⊕ s₀ ⊕ s) (MvPolynomial J O)[G],
      (∀ i, B₀ i ∈ tiedRows u (ribetGenerators δ s₀ s) p τ φ ε (tiedNormaliser J (γ π) a c₁)) ∧
      addVal O (Matrix.comp _ _ r r O (B₀.map (polyActionAtZero J (ρ π)))).det ≤ b₀ :=
    exists_tiedRows_addVal_det_le u (ρ π) hρ_span (hργ π) hc₁ a hz hb₀
  -- The characters: matrices `R.tiedMatrix i` of tied rows for all characters.
  obtain ⟨R⟩ : Nonempty (CharacterRows u ξ δ o s₀ s (γ π) a c₁ C p τ φ ε ty b) :=
    nonempty_characterRows u hξδ hδ_poly hz (hξγ π) c₁ hp hε hq ty (fun e Z hZ ↦ (hb e Z hZ).1)
      fun e Z hZ ↦ (hb e Z hZ).2
  -- The gluing, with the weights `∏ R.coeff e (i e)`. At `x ∈ 𝓧` the value is `F x * ∏ R.detSum e`.
  let c₀ : O := (∏ v, (o v).eval 1) * C ^ #s
  let D (x : 𝓧) : MvPolynomial J O :=
    (Matrix.comp _ _ r r (MvPolynomial J O) (B₀.map (polyAction J (ρ x)))).det
  let F (x : 𝓧) : MvPolynomial J O := D x * .C (C * c₀ ^ t)
  obtain ⟨f, hf_mem, hf_val⟩ : ∃ f : S,
      (∀ ω : G →₀ O, f.1 * (fun x : Y ↦ MvPolynomial.C
        (algebraMap O L (linearCombination O (fun g ↦ u x g - 1) ω).det)) ∈ 𝒥) ∧
      ∀ x : 𝓧, f.1 x = algebraMap (MvPolynomial J O) (MvPolynomial J L) (∑ i : ∀ e, Fin (R.count e),
        (∏ e, R.coeff e (i e)) * (.C C * D x * ∏ e,
          ((R.tiedMatrix i).map (polyChar J (ξ e))).det)) :=
    exists_traceIdeal_multiplier_eq_sum_det u 𝒥 blockEquiv ρ hξ₀ hu_block h𝒥 hz (γ := γ π) (a := a)
      (c₁ := c₁)
      hkξ hkρ (μ₀ := .C C) (hq 0) B₀ hB₀ (fun i : ∀ e, Fin (R.count e) ↦ ∏ e, R.coeff e (i e))
        R.tiedMatrix R.tied
  have hf_eq (x : 𝓧) :
      f.1 x = algebraMap (MvPolynomial J O) (MvPolynomial J L) (F x * ∏ e, R.detSum e) := by
    rw [hf_val x]
    congr 1
    calc ∑ i : ∀ e, Fin (R.count e), (∏ e, R.coeff e (i e)) *
          (.C C * D x * ∏ e, ((R.tiedMatrix i).map (polyChar J (ξ e))).det)
        = .C C * D x * ∑ i : ∀ e, Fin (R.count e),
          (∏ e, R.coeff e (i e)) * ∏ e, ((R.tiedMatrix i).map (polyChar J (ξ e))).det := by
          simp only [Finset.mul_sum, mul_left_comm (∏ e, R.coeff e _)]
      _ = .C C * D x * (.C c₀ ^ t * ∏ e, R.detSum e) := by
        rw [R.sum_prod_coeff_mul_prod_det_tiedMatrix]
      _ = F x * ∏ e, R.detSum e := by
          simp only [F, map_mul, map_pow]
          ring
  have hf_coeff (x : 𝓧) (i : J →₀ ℕ) (hi : i ≤ ∑ j : J, .single j 1) :
      (f.1 x).coeff i = algebraMap O L
        (if ∑ j, .single j 1 = i then constantCoeff (F x * ∏ e, R.multiplier e) else 0) := by
    rw [hf_eq, ← coeff_mul_prod_of_mem_colon ty R.correction_mem_colon R.add_eq_mul_prod (F x) hi]
    exact MvPolynomial.coeff_map (algebraMap O L) (F x * ∏ e, R.detSum e) i
  refine ⟨constantCoeff (F π * ∏ e, R.multiplier e),
    ⟨C_det_linearCombination_mem u h𝒥.X_mem h𝒥.charpoly_coeff_mem hz, fun ω x ↦ ?_,
      f, hf_mem, fun x i hi ↦ ?_, ?_⟩, ?_⟩
  · simp only [det_linearCombination_sub_one_eq_zero u blockEquiv hξ₀ (hu_block x), map_zero]
  · rw [hf_coeff x i hi.le, ite_eq_right hi.ne', map_zero]
  · rw [hf_coeff π _ le_rfl, ite_eq_left rfl]
  · -- Add up the valuations.
    have hD_eq : constantCoeff (D π) =
        (Matrix.comp _ _ r r O (B₀.map (polyActionAtZero J (ρ π)))).det := by
      simp [D, polyActionAtZero, det_apply']
    have hD : addVal O (constantCoeff (D π)) ≤ b₀ := by rwa [hD_eq]
    have hc₀ : addVal O c₀ = ∑ v, addVal O (eval 1 (o v)) + #s * addVal O C := by
      simp [c₀, addVal_prod]
    calc addVal O (constantCoeff (F π * ∏ e, R.multiplier e))
        = addVal O (constantCoeff (D π)) + (addVal O C + t * addVal O c₀) +
            addVal O (constantCoeff (∏ e, R.multiplier e)) := by
          simp only [F, map_mul, MvPolynomial.constantCoeff_C, addVal_mul, addVal_pow, nsmul_eq_mul]
      _ ≤ b₀ + (addVal O C + t * addVal O c₀) +
            (∑ e, b e + (Fintype.card J + t * #s) * addVal O C) :=
          add_le_add (add_le_add hD le_rfl) R.addVal_constantCoeff_prod_le
      _ = b₀ + (∑ e, b e + t * (∑ v, addVal O (eval 1 (o v)) + 2 * #s * addVal O C) +
            (Fintype.card J + 1) * addVal O C) := by
          rw [hc₀]
          ring

end Lemma

end New.Selmer

end RibetFirstOrder
