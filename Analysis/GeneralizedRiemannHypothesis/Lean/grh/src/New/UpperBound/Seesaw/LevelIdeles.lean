import New.OneLift.ComparisonOperator.ExchangeData
import New.UpperBound.Seesaw.EdgePairEvaluation

/-!
# Valuations of the chosen ideles, and lattices and levels at the chosen places

Facts at the finite places about the chosen data `D : New.Data P` and a tame character `ϑ`. The
notions used:
* `New.Data.piM` is the integer `π̄₀ π̄₁` of `E`, whose product with its conjugate is `M = p₀ p₁`
  (`New.Data.M`). The chosen places are the prime divisors of `π̄₀ π̄₁`.
* `New.Data.chosenIdele` is a finite idele that generates the ideal `(π̄₀ π̄₁)` and is `1` away from
  the chosen places.
* `New.Data.ideleA` is the idele `a = α / star chosenIdele`, with `α` the idele of the Weil data.
* `New.Data.gradingY k` presents the hermitian space `Y_k = New.Data.spaceY k` as an orthonormal
  part plus a string of `2 ϱ + 1 - k` vectors.
* `New.levelOf w H` is the group of integral elements of the finite adelic unitary group whose
  reductions at the places `w i` form an element of `H`.

## Main definitions and results

* `New.Data.v_chosenIdele`: `New.Data.chosenIdele` has the valuations of `π̄₀ π̄₁` at every finite
  place.
* `New.Data.v_gradingY_genericConst_eq_ideleA_mul_star`: the constant of the grading
  `New.Data.gradingY` has the valuations of `a ā`.
* `New.Data.spansLattice_gradingY`: the graded space `Y_k` carries the lattice with basis
  `New.gradedLatticeBasis`.
* `New.Data.chosenLevel_inf_trivialOn_le`: elements of principal level `π̄₀ π̄₁` that are `1` at the
  places `ϑ.Q` lie in the trivial level at the places `New.Data.levelPlaces`.

## Relation to the literature

These are auxiliary facts about the data `New.Data`; no external source is cited.
-/

namespace New.Data

open Rows Ideal WeilData Valued Parameters Gf stdLevel
open scoped NumberField

variable {P : Parameters} (D : Data P)

/-- The ideal of `E` spanned by `D.piM`, an integer of `K` of norm `p₀ p₁` viewed in `E`, has norm
`M ^ f`, where `M = D.M = p₀ p₁` and `f = D.f` is the number of infinite places of `E`. -/
lemma absNorm_piM : absNorm (span {D.piM}) = D.M ^ D.f := by
  simp [span_piM, prod_q_chosenPlace]

/-- At each finite place `w` of `E`, the finite idele `D.chosenIdele` has the same valuation `v` as
`D.piM`, an integer of `K` of norm `p₀ p₁` viewed in `E`, whose ideal the idele generates. -/
lemma v_chosenIdele (w : FinPlace D.E) :
    v (D.chosenIdele.val w) = v ((algebraMap (𝓞 D.E) (Ô D.E) D.piM).val w) :=
  calc v (D.chosenIdele.val w) = .exp (-multiplicity w.asIdeal (span {D.piM})) :=
        D.valued_chosenIdele w
    _ = w.intValuation D.piM := (w.intValuation_eq_exp_neg_multiplicity D.piM_ne_zero).symm
    _ = v (algebraMap D.E (LocField w) D.piM) := (v_algebraMap_eq_intValuation D.piM).symm
    _ = v ((algebraMap (𝓞 D.E) (Ô D.E) D.piM).val w) := rfl

/-- Let `D` be admissible data, with field `E = D.E` and level `M = D.M = p₀ p₁`, a natural number.
At each finite place `w` of `E`, with `v` the valuation of the completion of `E` at `w`, the norm
`α ᾱ` of the finite idele `α = WeilData.α` in the Weil data of `E` has the valuation of `a ā M`.
Here `a = D.ideleA = α / star D.chosenIdele`, and `D.chosenIdele` generates an ideal whose product
with its conjugate is `(M)`. -/
lemma v_alpha_mul_star_eq_ideleA_norm_mul_M (w : FinPlace D.E) :
    v (((WeilData.α (E := D.E)).val * star (WeilData.α (E := D.E)).val) w) =
      v ((D.ideleA.val * star D.ideleA.val) w) * w.valuation D.E (D.M : D.E) := by
  have h_α : D.ideleA.val * (star D.chosenIdele).val = (WeilData.α (E := D.E)).val := by
    rw [← Units.val_mul, ideleA, div_mul_cancel]
  have h_piM_mul_star : ((D.piM * star D.piM : 𝓞 D.E) : D.E) = D.M := by
    rw [D.piM_mul_star]
    rfl
  -- `D.chosenIdele` has the valuations of `D.piM`, whose norm is `M`.
  have h_norm : v ((D.chosenIdele * star D.chosenIdele.val) w) =
      w.valuation D.E (D.M : D.E) := by
    simp [← h_piM_mul_star, v_chosenIdele]
  rw [← h_α, ← h_norm]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Let `D` be admissible data, with field `E = P.E D.towerExp`, level `M = D.M = p₀ p₁` and
`D.m = 2 ϱ + 2` lifts (`ϱ = D.ϱ`), and let `k ≤ 2 ϱ + 1`, that is `k < D.m`. The grading
`D.gradingY k` presents the hermitian space `Y_k = D.spaceY k` over `E` as an orthonormal part plus
a string of `2 ϱ + 1 - k` vectors with antidiagonal Gram matrix, and carries the constant
`genericConst = -(j M δ_E)⁻¹` of `E`. At each finite place `w` of `E`, with `v` the valuation of
the completion at `w`, this constant has the valuation of `a ā`.
Here `j` and `α` are the purely imaginary element and the finite idele of the Weil data of `E`,
`δ_E = P.deltaE D.towerExp` generates the different of `E`, and
`a = D.ideleA = α / star D.chosenIdele`. -/
lemma v_gradingY_genericConst_eq_ideleA_mul_star {k : ℕ} {hk : k ≤ 2 * D.ϱ + 1} (w : FinPlace D.E) :
    v (((D.gradingY k hk).genericConst.val : 𝔸f D.E) w) =
      v ((D.ideleA.val * star D.ideleA.val) w) := by
  let j : D.E := WeilData.j
  let α : (𝔸f D.E)ˣ := WeilData.α
  -- The order of `j α ᾱ` is minus the order of the different, which `δ_E` generates, so
  -- `j α ᾱ δ_E` is a unit at `w`. As `α ᾱ` has the valuation of `a ā M`, so is `j M δ_E a ā`.
  have h_deltaE : w.valuation D.E (P.deltaE D.towerExp) =
      .exp (-multiplicity w.asIdeal (differentIdeal ℤ (𝓞 D.E))) := by
    rw [w.valuation_of_algebraMap, differentIdeal_eq_span_deltaE,
      w.intValuation_eq_exp_neg_multiplicity
        (ne_zero_of_differentIdeal_eq_span differentIdeal_eq_span_deltaE)]
  have h_unit : v ((algebraMap D.E (𝔸f D.E) j * α.val * star α.val : 𝔸f D.E) w) *
      w.valuation D.E (P.deltaE D.towerExp) = 1 := by
    refine (congrArg₂ HMul.hMul (v_weilData_j_mul_alpha_mul_star w) h_deltaE).trans ?_
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have h_genericConst : v (((D.gradingY k hk).genericConst.val : 𝔸f D.E) w) =
      (w.valuation D.E j * (w.valuation D.E (D.M : D.E) * w.valuation D.E
        (P.deltaE D.towerExp)))⁻¹ := by
    change v (algebraMap D.E (LocField w) (-(j * (D.M * P.deltaE D.towerExp) : D.E)⁻¹)) = _
    rw [v_algebraMap_eq_valuation, Valuation.map_neg, map_inv₀, map_mul, map_mul]
  refine h_genericConst.trans (inv_eq_of_mul_eq_one_right ?_)
  calc w.valuation D.E j * (w.valuation D.E (D.M : D.E) * w.valuation D.E (P.deltaE D.towerExp)) *
        v ((D.ideleA.val * star D.ideleA.val) w)
    _ = w.valuation D.E j * v ((α.val * star α.val : 𝔸f D.E) w) *
        w.valuation D.E (P.deltaE D.towerExp) := by
        rw [D.v_alpha_mul_star_eq_ideleA_norm_mul_M]
        ac_rfl
    _ = 1 := by simpa [v_algebraMap_eq_valuation, mul_assoc] using h_unit

/-- Let `k ≤ 2 ϱ + 1`, where `ϱ = D.ϱ`. The grading `D.gradingY k` presents the hermitian space
`Y_k = D.spaceY k` over `E` as an orthonormal part, with last vector `y`, plus a string of
`s = 2 ϱ + 1 - k` vectors. Let `a = D.ideleA`, let `π = D.piNIdele` be the principal idele of the
integer `D.piN` of `E` with `π π̄ = D.N`, and let `u = D.latticeScale k = (a / ā) ^ ⌈(2 ϱ + 2 -
k) / 2⌉`. Then the finite adelic basis `xFin` of `Y_k` spans the same lattice over `Ô` as the
following basis `New.gradedLatticeBasis`. For odd `s`, multiply the string vectors by `u` and
replace `y` by `y / π̄ + u z / (π π̄)`, with `z` the middle vector of the string. For even `s`,
multiply the first half of the string by `u / a` and the second half by `u ā`. All other vectors are
unchanged. -/
lemma spansLattice_gradingY (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) :
    (D.gradingY k hk).SpansLattice D.ideleA D.piNIdele (D.latticeScale k) := by
  have hk_lt : k < D.m := by grind
  -- By definition of `SpansLattice` and of the index equivalence of `D.gradingY k`:
  change ∃ g ∈ intGL (D.Y k) (Ô D.E), (D.spaceY k).xFin.val =
    gradedLatticeBasis (D.indexEquivY k hk_lt) D.ideleA D.piNIdele (D.latticeScale k) * g.val
  obtain ⟨g, -, h_xFin⟩ := D.exists_spaceY_xFin_eq k hk_lt
  exact ⟨g, g.property, h_xFin⟩

/-- Let `ϑ` be a tame character: an automorphic character of `U(1)` of weight `0` whose tame part, a
family of characters of the residue fields, is trivial outside the finite set of places `ϑ.Q`. Let
`g` in the finite adelic unitary group indexed by `n` be integral with reduction `1` at the chosen
places (`D.chosenLevel`) and have component `1` at the places of `ϑ.Q` (`trivialOn`). Then `g` is
integral with reduction `1` at all places of `D.levelPlaces ϑ`, which are the chosen places and
those of `ϑ.Q`: it lies in `levelOf` at these places for the trivial group `⊥` of reductions. -/
lemma chosenLevel_inf_trivialOn_le (ϑ : D.TameChar) {n : Type} [Fintype n] [DecidableEq n] :
    D.chosenLevel (n := n) ⊓ trivialOn n ϑ.Q ≤ levelOf (n := n) (D.levelPlaces ϑ).placeAt ⊥ := by
  rintro g ⟨hg_level, hg_trivial⟩
  obtain ⟨hg_integral, h_red⟩ : ∃ hg_integral : g ∈ stdLevel D.E n,
      reduceFamily D.chosenPlace ⟨g, hg_integral⟩ ∈ (⊥ : Subgroup _) :=
    mem_levelOf.1 hg_level
  rw [Subgroup.mem_bot] at h_red
  refine mem_levelOf.2 ⟨hg_integral, Subgroup.mem_bot.2 ?_⟩
  ext1 (w | w)
  · -- At the chosen places the reduction is `1`, as `g` lies in `D.chosenLevel`.
    exact congrFun h_red w
  · -- At the places of `ϑ.Q` the component itself is `1`.
    exact reduceAt_eq_one_of_atPlace (mem_trivialOn.1 hg_trivial w.val w.property)

end New.Data
