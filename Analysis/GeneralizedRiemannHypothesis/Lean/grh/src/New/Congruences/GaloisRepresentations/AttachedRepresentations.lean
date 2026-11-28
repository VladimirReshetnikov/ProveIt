import New.Congruences.GaloisRepresentations.SelmerHypotheses
import New.OneLift.HeckeValues.TwistedRatio

/-!
# Lift settings and conjugate self-duality of attached Galois representations

This file shows that good tuples of labels form lift settings with the descent pairs of the data.
It also shows that, for a main pair, the constant label `X - 1` forms a lift setting for the lift
from `U(1)`. It bounds the `ℓ`-adic valuation of `p_i ^ d - 1` and gives basic facts on lattices
in a representation. It proves that representations attached to Hecke eigenforms are conjugate
self-dual. It also shows that representations of a type arise from labelled eigenforms and are
preserved by twisting with avatars.

## Main definitions and results

* `New.Selmer.isConjSelfDual_of_attached`: a Galois representation `r` of rank `n` attached to a
  Hecke eigenform (`New.GaloisRep.Attached`) satisfies `New.Selmer.IsConjSelfDual`. In particular,
  tr r(g^c) = χ(g)^(n-1) tr r(g⁻¹) with χ = `New.Selmer.cyclotomicInv`. The Hecke operators at w and
  w̄ are dual (`New.heckeSplit_dual`), which gives the relation for most Frobenii. It passes to
  every g along the filter `New.mostFrobeniiAt`.
* `New.Selmer.isRepOfType_of_hasProductLabel`: the representation attached to a labelled eigenform
  is a representation of a type.

Notions from other files:
* `New.Data.descentPair`: The j-th descent pair (`New.DescentPair`) for ϑ: W = W_j of rank r,
  V = I_{r+t}, the character μ_j⁰ϑ of weight −w_j, and the places `New.Data.levelPlaces`.
* `New.Data.CriticalPair.IsMainPair`: A pair `p = (p.character, z)` with `p.character` of weight
  `-c` is a main pair for `j` if the index type `RankOneIndex z` has `2 z` elements and `2 ≤ z`
  (`HasLiftRank`), `m < z ≤ r`, `1 ≤ j ≤ m`, the tame part of `p.character` is `D.chiMLocal ^ j`
  (`D.chiMLocal` the tame character of the data), and `w_j + r - t ≤ c ≤ w_j` at every infinite
  place, with `w_j = D.liftWeight j`.
* `New.Selmer.IsConjSelfDual`: `R` is continuous, has non-degenerate trace form, and is conjugate
  self-dual up to twist on traces, tr R(g^c) = χ(g)^(t-1) tr R(g⁻¹), with `g^c = c g c`
  (`New.conjGal`) and χ = `New.Selmer.cyclotomicInv`.
* `New.Selmer.IsLiftSetting`: the descent pair `O` with the labels `c` is a lift setting for the
  twist `ϑ`.
* `New.Selmer.IsRepOfType`: `R` is a conjugate self-dual representation of level `S`, and inertia
  at the chosen places acts through the roots of the labels `c`.

## Relation to the literature

For sources see `Lib.GaloisRep.Main.OddRank`, `Lib.PadicHodge.Crystalline.Regularity` and
`New.Congruences.GaloisRepresentations.RowsFromEigensystems`.
-/

noncomputable section

namespace New.Selmer

/-!
## Lift settings for the descent pairs and for the lift from U(1)

* `New.Selmer.isLiftSetting_descentPair`: the good tuples of labels form a lift setting with the
  descent pair of index `j`.
* `New.Selmer.isLiftSetting_mainPair`, `New.Selmer.trivialLift_mem_range_typeProjection`: for a main
  pair, the constant label `X - 1` forms a lift setting for the lift from `U(1)`. The form
  `trivialLift`, a multiple of the theta lift of the constant function `1`, lies in the range of the
  corresponding idempotent.
-/

section AptInstances

open Polynomial Fintype Finset

/-- If a unit `y` is not a root of `q`, then `1` is not a root of `q` with its roots multiplied by
`y⁻¹`. -/
lemma not_isRoot_one_scaleRoots_inv {K : Type*} [Field K] {q : K[X]} {y : Kˣ}
    (hy : ¬q.IsRoot y.val) : ¬(q.scaleRoots (y⁻¹).val).IsRoot 1 := by
  rw [IsRoot.def, ← y.inv_mul, scaleRoots_eval_mul]
  simpa using hy

attribute [local instance low] Fintype.ofFinite

variable {P : Parameters} (D : Data P) (ϑ : D.Twist)

/-- Let `j` be a lift index, `1 ≤ j ≤ D.m`, and `ϑ` a twist. Let `c` be a good family of polynomials
over the residue fields at the chosen places: each is a label of degree `D.r` (monic, squarefree,
nonzero at `0`) that vanishes at no `q₂`-th root of unity of its field, `q₂ = P.q₂ D.towerExp`, and
over each of `p₀`, `p₁` one of them is primitive. The `j`-th descent pair with the labels `c` is a
lift setting for `ϑ`. -/
theorem isLiftSetting_descentPair (j : D.LiftIndex)
    {c : ∀ x : Σ i : Fin 2, D.ChosenPlace i, (ResField (D.chosenPlace x))[X]}
    (hc : c ∈ D.goodTupleFamilies) : IsLiftSetting (D.descentPair ϑ j) c ϑ := by
  classical
  -- Over each of the two primes, the labels form a good tuple.
  have h_good (i : Fin 2) :
      (∀ w : D.ChosenPlace i, IsAllowedPolynomial (P.q₂ D.towerExp) (card D.RowIndex) (c ⟨i, w⟩)) ∧
      ∃ w : D.ChosenPlace i, IsPrimitivePolynomial (card D.RowIndex) (c ⟨i, w⟩) :=
    mem_goodTuples.1 (mem_piFinset.1 (mem_map_equiv.1 hc) i)
  refine
    { toLevelPlaces_eq := rfl
      exists_tamePart_eq_chiMLocal_zpow_mul := ⟨j, j.2, rfl⟩
      odd := by simp [D.card_rowIndex, D.r_odd, D.t_odd, DescentPair.rankDiff]
      rank_le := by simp [D.card_rowIndex, DescentPair.rankDiff]
      isLabel w := ((h_good w.1).1 w.2).isLabel
      exists_primitive_or_one i := ?_
      not_isRoot_scaledTypePoly w := ?_ }
  · obtain ⟨w, hw⟩ := (h_good i).2
    exact ⟨⟨i, w⟩, w.2.2, .inl ⟨D.card_rowIndex, hw⟩⟩
  · -- `1` is a root of the scaled type polynomial exactly when `x`, the unit naming the character
    -- at `w`, is a root of `c w`; it is a root of unity of order dividing `P.q₂ D.towerExp`, so it
    -- is not.
    have hϑ_one : ϑ.tamePart ((D.levelPlaces ϑ).chosenPlace w) = 1 :=
      ϑ.toTameChar.tamePart_eq_one_of_isChosen (D.isChosen_levelPlaces_chosenPlace ϑ w)
    set v : FinPlace D.E := (D.descentPair ϑ j).chosenPlace w
    set x : (ResField v)ˣ := charName (faithfulChar (ResField v)) ((D.descentPair ϑ j).tamePart v)
    have h_not_root : ¬(c w).IsRoot x.val :=
      ((h_good w.1).1 w.2).not_isRoot
        (charName_pow_eq_one (k := ResField v) (D.chiMLocal_zpow_mul_pow_eq_one _ hϑ_one))
    show ¬((c w).scaleRoots
      (charName (faithfulChar (ResField v)) ((D.descentPair ϑ j).tamePart v)⁻¹).val).IsRoot 1
    rw [map_inv]
    exact not_isRoot_one_scaleRoots_inv h_not_root

variable {D} {p : D.CriticalPair} {j : ℕ}

/-- Let `p = (ν, z)` be a main pair for `j` (`New.Data.CriticalPair.IsMainPair`): `D.m < z ≤ D.r`,
`1 ≤ j ≤ D.m`, the character `ν` of `U(1)` has tame part `D.chiMLocal ^ j`, and its weight `-c`
satisfies `w_j + D.r - D.t ≤ c ≤ w_j` with `w_j = D.liftWeight j`. Let `ϑ` be a twist. The descent
pair of `p.lValueData hp.hasLiftRank ϑ`, the data for the lift of `ν ϑ` from `U(1)` to `U(2 z)`, has
a space `W` of rank one. With every label equal to `X - 1` it is a lift setting for `ϑ`
(`New.Selmer.IsLiftSetting`). -/
theorem isLiftSetting_mainPair (hp : p.IsMainPair j) :
    IsLiftSetting (p.lValueData hp.hasLiftRank ϑ).descentPair
      (fun _ : (p.lValueData hp.hasLiftRank ϑ).descentPair.ChosenIndex ↦ X - 1) ϑ := by
  have h_fit : p.HasLiftRank (Data.RankOneIndex p.z) := hp.hasLiftRank
  have hz : p.z ∈ Set.Ioc D.m D.r := hp.z_mem
  -- The rank `card Unit` of `W` is `1` and the difference `rankDiff` is `2 z - 1`; both are odd.
  refine
    { toLevelPlaces_eq := rfl
      exists_tamePart_eq_chiMLocal_zpow_mul := ⟨j, hp.j_mem,
        show p.tamePart * ϑ.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart by rw [hp.tamePart_eq]⟩
      odd := by grind [card_unique]
      rank_le := by grind [card_unique]
      -- `map_one` is kept out of `simp` because it would undo the rewriting of `1` as `C 1`.
      isLabel i := by simp [IsLabel, ← C_1, Monic, -map_one, separable_X_sub_C.squarefree]
      exists_primitive_or_one k := ⟨⟨k, D.chosenEquiv k 1⟩, (D.chosenEquiv k 1).2.2, by simp⟩
      not_isRoot_scaledTypePoly i := ?_ }
  -- The scaled type polynomial has the root `1` only if the tame part of `ν` is trivial at the
  -- place, and a main pair is ramified.
  have h_ram (w : FinPlace D.E) : p.tamePart w ≠ 1 ↔ D.IsChosen w := hp.isRamified w
  simp [MulEquiv.map_eq_one_iff, scaledTypePoly, ← C_1, -map_one, isChosen_chosenPlace, h_ram,
    sub_eq_zero]

/-- Let `p = (ν, z)` be a main pair for `j`: `D.m < z ≤ D.r`, `1 ≤ j ≤ D.m`, the character `ν` of
`U(1)` has tame part `D.chiMLocal ^ j`, and its weight `-c` satisfies `w_j + D.r - D.t ≤ c ≤ w_j`
with `w_j = D.liftWeight j`. Let `ϑ` be a twist and `Y = p.lValueData hp.hasLiftRank ϑ` the data for
the lift of `ν ϑ` from `U(1)` to `U(2 z)`. Then the form `Y.trivialLift`, a multiple of the theta
lift of the constant function `1`, lies in the range of the idempotent `typeProjection` of the
descent pair of `Y` with every label equal to `X - 1`. -/
theorem trivialLift_mem_range_typeProjection (hp : p.IsMainPair j) :
    (p.lValueData hp.hasLiftRank ϑ).trivialLift ∈
      (typeProjection (p.lValueData hp.hasLiftRank ϑ).descentPair
        fun _ : (p.lValueData hp.hasLiftRank ϑ).descentPair.ChosenIndex ↦ X - 1).range := by
  classical
  set Y := p.lValueData hp.hasLiftRank ϑ
  -- The label `X - 1` belongs to the trivial character of `GL₁`.
  have h_label (w : FinPlace D.E) (g : GL Unit (ResField w)) :
      (labelChar (faithfulChar (ResField w))
          (X - C (charName (faithfulChar (ResField w)) 1).1)).evalGL g = 1 := by
    rw [labelChar_X_sub_C]
    -- On `GL₁` the rank `1` part of a function is the function itself.
    exact (ite_eq_left (by simp)).trans ((evalGL_detChar 1 g).trans (MulChar.one_apply_coe g.det))
  have h_isLabel (i : Y.descentPair.ChosenIndex) :
      IsLabel (card Unit) (X - 1 : (ResField (Y.descentPair.chosenPlace i))[X]) :=
    (isLiftSetting_mainPair ϑ hp).isLabel i
  refine ⟨Y.trivialLift, ?_⟩
  -- The idempotent is the mean over the group, which fixes `Y.trivialLift`.
  show typeProjection Y.descentPair (fun _ ↦ X - 1) Y.trivialLift = Y.trivialLift
  simp_all [asAlgebraHom_eq_sum, tupleIdem, labelIdem, Y.formAction_trivialLift,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, prod_ne_zero_iff]

end AptInstances

/-!
## Divisors of the chosen group order, places above p₀ and p₁, and lattices

* `New.Selmer.levelPrime_pow_sub_one_dvd_chosenGroupOrder`,
  `New.Selmer.ellVal_levelPrime_pow_sub_one_le`: with `p_i = D.levelPrime i`, the number
  `p_i ^ d - 1` divides `New.Data.chosenGroupOrder` for `1 ≤ d ≤ r t`, which bounds its `ℓ`-adic
  valuation.
* `New.Selmer.IsLatticeIn.exists_algHom` and its companions: a lattice `u` in `R` has the same
  determinants and traces as `R`, is trivial where `R` is, and is continuous if `R` is.
-/

section CrudeBounds

open Matrix Finset Topology NeZero Data FinPlace

attribute [local instance low] Fintype.ofFinite

variable {P : Parameters} (D : Data P) (ℓ : ℕ) [ThePrime ℓ]
  {n : Type} [Fintype n] [DecidableEq n] {O : CoeffRing ℓ}

/-! ### The primes `p₀`, `p₁` and the places above them -/

/-- For `1 ≤ d ≤ D.r * D.t` and each of the two primes `p_i = D.levelPrime i`, the number
`p_i ^ d - 1` divides `D.chosenGroupOrder`. That number is the product, over the chosen places above
`p₀` and `p₁`, of the orders of `GL (D.r * D.t)` over the residue fields. -/
lemma levelPrime_pow_sub_one_dvd_chosenGroupOrder {i : Fin 2} {d : ℕ}
    (hd : d ∈ Set.Icc 1 (D.r * D.t)) : D.levelPrime i ^ d - 1 ∣ D.chosenGroupOrder := by
  -- It is the first factor of the order of `GL_d` over the residue field (with `p_i` elements)
  -- of a place `w` above `p_i`, and `chosenGroupOrder` is a multiple of the product of these
  -- orders.
  let w : D.ChosenPlace i := D.chosenEquiv i 1
  have h_above : ↑(D.levelPrime i) ∈ w.val.asIdeal := w.2.2
  calc
    D.levelPrime i ^ d - 1 ∣ Nat.card (GL (Fin d) (ResField w.1)) := by
      grw [card_GL_field, ← dvd_prod_of_mem _ (mem_univ ⟨0, hd.1⟩), Fintype.card_eq_nat_card,
        card_ResField, D.q_eq_levelPrime h_above, pow_zero]
    _ ∣ Nat.card (∀ x, GL (Fin d) (ResField (D.chosenPlace x))) := by
      grw [Nat.card_pi, ← dvd_prod_of_mem _ (mem_univ ⟨i, w⟩), chosenPlace]
    _ ∣ D.chosenGroupOrder := D.card_GL_dvd_chosenGroupOrder (by simpa using hd.2)

/-- For each of the two primes `p_i = D.levelPrime i` and each `d` with `1 ≤ d ≤ D.r * D.t`, the
`ℓ`-adic valuation of `p_i ^ d - 1` is at most that of `D.chosenGroupOrder`. -/
lemma ellVal_levelPrime_pow_sub_one_le (i : Fin 2) {d : ℕ} (hd : d ∈ Set.Icc 1 (D.r * D.t)) :
    ellVal (D.levelPrime i ^ d - 1 : PadicAlgCl ℓ) ≤ padicValNat ℓ D.chosenGroupOrder := by
  simpa [pos, ellVal_natCast, ne] using
    dvd_iff_ellVal_le.1 (levelPrime_pow_sub_one_dvd_chosenGroupOrder D hd).natCast

/-- Every finite set `T` of finite places of `E = D.E` inside `placesAboveM D` (the places above the
primes `p₀`, `p₁` of `D`) has at most `4 * D.f` elements, where `D.f` is the number of infinite
places of `E`. -/
lemma card_le_of_subset_placesAboveM {T : Finset (FinPlace D.E)} (hT : ↑T ⊆ placesAboveM D) :
    #T ≤ 4 * D.f := by
  -- A place above `p_i` is chosen or the conjugate of a chosen one, and `f` places above each
  -- `p_i` are chosen. The `Fin 2` part of `x` says whether to conjugate.
  let place (x : Fin 2 × Sigma D.ChosenPlace) : FinPlace D.E := star^[x.1] x.2.snd.val
  have surj : Set.SurjOn place (SetLike.coe univ) T := fun v hv ↦ by
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.levelPrime i : NumberField.RingOfIntegers D.E) ∈ v.asIdeal :=
      hT hv
    by_cases hG : D.IsChosen v
    · exact ⟨⟨0, i, v, hG, hi⟩, by simp [place]⟩
    · exact ⟨⟨1, i, star v, (D.isChosen_star_iff hi).2 hG, by simpa⟩, by simp [place]⟩
  have card_chosen (i : Fin 2) : Fintype.card (D.ChosenPlace i) = D.f := by
    simpa using D.card_chosenPlace i
  have h_le : #T ≤ #(univ : Finset (Fin 2 × Sigma D.ChosenPlace)) :=
    card_le_card_of_surjOn place surj
  simpa [card_chosen, ← mul_assoc, ← two_mul] using h_le

/-- Let `p₀ = D.levelPrime 0` and `p₁ = D.levelPrime 1` be the two primes of the data `D`, and `ℓ`
a prime. Some finite place `w` of `D.E` is chosen (`New.Data.IsChosen`: it divides the integer
`D.piM`), lies above `p₀` or `p₁` (`placesAboveM D`) but not above `ℓ`, and has a residue field of
order `w.q` equal to `p₀` or `p₁`. -/
lemma exists_chosen_notMem_placesDividing {P : Parameters} (D : Data P) (ℓ : ℕ) [ThePrime ℓ] :
    ∃ (w : FinPlace D.E) (i : Fin 2),
      D.IsChosen w ∧ w ∈ placesAboveM D \ placesDividing D.E ℓ ∧ w.q = D.levelPrime i := by
  -- Take a chosen place above a prime `D.levelPrime i` other than `ℓ`.
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, D.levelPrime i ≠ ℓ := D.levelPrime_injective.exists_ne ℓ
  obtain ⟨w, hw, hwi⟩ : D.ChosenPlace i := D.chosenEquiv i 1
  -- A place above both primes would have a residue field of two characteristics.
  have h_off : w ∉ placesDividing D.E ℓ :=
    fun hℓ ↦ hi ((charP_quotient w hwi).eq _ (charP_quotient w hℓ))
  exact ⟨w, i, hw, ⟨⟨i, hwi⟩, h_off⟩, D.q_eq_levelPrime hwi⟩

variable {D ℓ} {R : AbsGal D →* GL n (PadicAlgCl ℓ)} {u : AbsGal D →* Matrix n n O}

/-! ### Lattices in a representation -/

/-- If u is a lattice in R over O (`New.Selmer.IsLatticeIn`: R is conjugate to the image of u over
ℚ̄_ℓ), some injective O-algebra map F from matrices over O to matrices over ℚ̄_ℓ sends u(g) to R(g)
and preserves determinants and traces. -/
lemma IsLatticeIn.exists_algHom (h : IsLatticeIn R u) :
    ∃ F : Matrix n n O →ₐ[O] Matrix n n (PadicAlgCl ℓ),
      -- (a) `F` is injective and carries `u` to `R`
      Function.Injective F ∧
      (∀ g : AbsGal D, F (u g) = R g) ∧
      -- (b) `F` keeps determinants and traces
      ∀ A : Matrix n n O, (F A).det = A.det.val ∧ (F A).trace = A.trace.val := by
  obtain ⟨Q : ConjAct (GL n (PadicAlgCl ℓ)), hQ⟩ := h
  -- `F` maps the entries into the algebraic closure and then conjugates by `Q`.
  refine ⟨(MulSemiringAction.toAlgHom O _ Q).comp (Algebra.ofId O (PadicAlgCl ℓ)).mapMatrix,
    (MulAction.injective Q).comp (map_injective Subtype.coe_injective),
    fun g ↦ (eq_inv_smul_iff (g := Q)).1 (hQ g).symm, fun A ↦ ?_⟩
  let q : GL n (PadicAlgCl ℓ) := ConjAct.ofConjAct Q
  change (q.val * A.map O.val.val * q⁻¹.val).det = _ ∧ (q.val * A.map O.val.val * q⁻¹.val).trace = _
  rw [det_units_conj, trace_units_conj]
  simp [trace, det_apply]

/-- A lattice in a continuous representation is continuous. -/
lemma IsLatticeIn.continuous (h : IsLatticeIn R u) (hR : Continuous R) : Continuous u := by
  -- After the embedding of the entries, `u` is a fixed conjugate of `R`.
  obtain ⟨Q, hQ⟩ := h
  exact IsInducing.subtypeVal.matrix_map.continuous_iff.2 (.congr (by fun_prop) hQ)

/-- A lattice in `R` is trivial wherever `R` is trivial. -/
lemma IsLatticeIn.eq_one (h : IsLatticeIn R u) {g : AbsGal D} (hg : R g = 1) : u g = 1 := by
  obtain ⟨F, hF_inj, hF_u, -⟩ := h.exists_algHom
  exact hF_inj (by simp [hF_u, hg])

/-- If `u` is a lattice in `R` (`IsLatticeIn R u`), then for every `g` in `AbsGal D` the trace of
`u g`, read in `ℚ̄_ℓ`, equals the trace of `R g`. -/
lemma IsLatticeIn.trace_eq (h : IsLatticeIn R u) (g : AbsGal D) :
    (u g).trace.val = (R g).val.trace := by
  obtain ⟨F, -, hF_u, hF_inv⟩ := h.exists_algHom
  rw [← hF_u, (hF_inv _).2]

end CrudeBounds

end New.Selmer

/-! ## Conjugate self-duality of attached representations -/

section ConjugateSelfDual

open Matrix Polynomial Filter Fintype New.GaloisRep

/-- Let a nonzero `f` in rank `k + 1` be spherical at the split place `w` with Hecke polynomial
`Q w` and at `star w` with Hecke polynomial `Q (star w)` (`New.HasHeckePolyAt`). Then the constant
coefficient of `Q w` times the `k`-th coefficient of `Q (star w)` is `q ^ k` times the linear
coefficient of `Q w`, where `q` is the order of the residue field at `w`. -/
lemma New.Selmer.coeff_zero_mul_coeff_star {P : Parameters} {D : Data P} {n M : Type} [Fintype n]
    [DecidableEq n] {f : Gf D.E n → M → ℂ} (hf : f ≠ 0) {Q : FinPlace D.E → ℂ[X]} {k : ℕ}
    (h_card : card n = k + 1) {w : FinPlace D.E}
    (hQw : ∃ hw : star w ≠ w, HasHeckePolyAt f w hw (Q w))
    (hQw_star : ∃ hw' : star (star w) ≠ star w, HasHeckePolyAt f (star w) hw' (Q (star w))) :
    (Q w).coeff 0 * (Q (star w)).coeff k = w.q ^ k * (Q w).coeff 1 := by
  -- `s j` and `u j` are the eigenvalues of the `j`-th Hecke operators at `w` and at `star w`.
  obtain ⟨hw, h_sph, s, hQs, hs⟩ := hQw
  obtain ⟨hw', h_sph', u, hQu, hu⟩ := hQw_star
  let σ := rightRegular ℂ (Gf D.E n) (M → ℂ)
  -- By `heckeSplit_dual`, for `card n = i + j` the `i`-th operator at `star w` followed by the
  -- scalar matrix `uniformizer w` is the `j`-th operator at `w`. For `i = 0` that scalar acts on
  -- `f` by `s (k + 1)`; then `i = 1` relates the eigenvalues.
  have h_rel (i j : ℕ) : card n = i + j →
      σ (ofSplitPlace hw (.scalar n (uniformizer w))) (heckeSplit σ hw' i f) =
        heckeSplit σ hw j f :=
    heckeSplit_dual hw i j h_sph (v_uniformizer _)
  have h_top := h_rel 0 (k + 1) (by omega)
  rw [heckeSplit, heckeGL_zero ((mem_sphericalAt_iff _).1 h_sph')] at h_top
  have h_one : u 1 * s (k + 1) = s k := by
    simpa [σ, smul_left_inj, smul_smul, hf, h_top, hs, hu] using h_rel 1 k (by omega)
  have h_zero : (Q w).coeff 0 = (-1) ^ (k + 1) * (w.q : ℂ) ^ (k + k.choose 2) * s (k + 1) := by
    simp [hQs, h_card, Nat.choose]
  have h_first : (Q w).coeff 1 = (-1) ^ k * (w.q : ℂ) ^ k.choose 2 * s k := by
    simp [hQs, h_card]
  have h_star : (Q (star w)).coeff k = -u 1 := by simp [hQu, h_card]
  rw [h_zero, h_first, h_star, ← h_one]
  ring

/-- Let f be an eigenform in rank n for the system Q of Hecke polynomials (`New.IsEigenform`), and
let r be an ℓ-adic Galois representation attached to Q. Then r satisfies
`New.Selmer.IsConjSelfDual`: it is continuous, has non-degenerate trace form, and is conjugate
self-dual on traces, tr r(cgc) = cyc(g)^{1−n} tr r(g⁻¹) for all g, with c complex conjugation and
cyc the cyclotomic character. -/
lemma New.Selmer.isConjSelfDual_of_attached {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {P : Parameters}
    {D : Data P} {n M : Type} [Fintype n] [DecidableEq n] {f : Gf D.E n → M → ℂ}
    {Q : FinPlace D.E → ℂ[X]} {r : GalRep ℓ D.E n} (h_eigen : IsEigenform f Q)
    (hr : Attached Q r) : IsConjSelfDual (card n) r := by
  -- With `card n = k + 1`, compare the coefficients of degree `0`, `1` and `k`, first for the
  -- Hecke polynomials at `w` and `star w`, then, in the limit, for characteristic polynomials.
  refine ⟨hr.continuous, hr.isTraceNondeg, fun g ↦ ?_⟩
  rcases h_card : card n with _ | k
  · -- In rank `0` both traces vanish.
    simp_all [card_eq_zero_iff]
  -- `conjGal` is a homeomorphism that carries Frobenius elements at `w` to Frobenius elements at
  -- `star w`, so `r`, read through `conjGal`, is attached to the system `w ↦ Q (star w)`.
  have h_open : Topology.IsOpenEmbedding (conjGal (E := D.E)) :=
    (Homeomorph.mk ⟨_, _, conjGal_conjGal, conjGal_conjGal⟩).isOpenEmbedding
  have h_conj : Attached (fun w : FinPlace D.E ↦ Q (star w)) r conjGal := by
    refine ⟨hr.continuous, hr.isTraceNondeg, h_open.isOpenMap, fun η hη ↦ ?_⟩
    refine (eventually_mostFrobenii_of_isOpenEmbedding h_open star
      (hr.eventually_norm_coeff_le hη)).mono fun y hy x hx ↦ ?_
    -- If `conjGal x` is Frobenius at `y.place`, then `x` is Frobenius at `star y.place`.
    let y' : FrobeniusDatum D.E :=
      ⟨star y.place, conjPlace y.valuationSubring, x, by simp [y.prime_q],
        y.isPlaceOver.conjPlace_star, by simpa [← hx] using y.isFrob_inv.conjPlace_conjGal⟩
    exact hy y' (by simp [y']) hx x rfl
  -- For most Frobenius elements `w` is prime to `ℓ`, so `cyclotomicInv` takes the value `w.q`, and
  -- `coeff_zero_mul_coeff_star` applies.
  have h_ev : ∀ᶠ y in mostFrobenii D.E, ιℓ ((Q y.place).coeff 0) * ιℓ ((Q (star y.place)).coeff k) =
      cyclotomicInv ℓ _ (PadicAlgCl ℓ) y.frob ^ k * ιℓ ((Q y.place).coeff 1) := by
    refine eventually_mostFrobenii
      (h_eigen.2.and <| (eventually_notMem_star_notMem ℓ ∅).and
        (star_injective.tendsto_cofinite h_eigen.2))
      fun y ⟨h_eig, ⟨_, _, hℓ⟩, h_eig'⟩ ↦ ?_
    have h_coeff := congrArg ιℓ
      (coeff_zero_mul_coeff_star h_eigen.1 h_card (h_eig y.prime_q) (h_eig' (by simp [y.prime_q])))
    simpa [cyclotomicInv_frob y hℓ] using h_coeff
  -- Along Frobenius elements tending to `g`, the coefficients tend to those of the characteristic
  -- polynomials.
  have h_lim : (r g).val.charpoly.coeff 0 * (r (conjGal g)).val.charpoly.coeff k =
      cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ k * (r g).val.charpoly.coeff 1 := by
    have h_left := h_conj.tendsto_charpoly_coeff (conjGal g) k
    rw [conjGal_conjGal] at h_left
    exact tendsto_nhds_unique_of_eventuallyEq ((hr.tendsto_charpoly_coeff g 0).mul h_left)
      ((tendsto_mostFrobeniiAt fun x : Gal(Ω/D.E) ↦ cyclotomicInv ℓ D.E (PadicAlgCl ℓ) x ^ k).mul
        (hr.tendsto_charpoly_coeff g 1))
      (h_ev.filter_mono inf_le_left)
  -- Up to sign these coefficients are `det (r g)`, the trace of `r (conjGal g)`, and `det (r g)`
  -- times the trace of `r g⁻¹`; the determinant cancels.
  have h_inv : (r g).val.charpoly =
      (-1) ^ card n * C (r g).val.det * (r g).val⁻¹.charpolyRev := by
    simpa using (r g⁻¹).val.charpoly_inv
  have h_zero : (r g).val.charpoly.coeff 0 = (-1) ^ (k + 1) * (r g).val.det := by
    simp [h_inv, h_card, coeff_zero_eq_eval_zero]
  have h_star : (r (conjGal g)).val.charpoly.coeff k = -(r (conjGal g)).val.trace := by
    simp [trace_eq_neg_charpoly_nextCoeff, nextCoeff, h_card]
  have h_first : (r g).val.charpoly.coeff 1 =
      (-1) ^ (k + 1) * (r g).val.det * -(r g⁻¹).val.trace := by
    rw [h_inv, h_card, ← C_1, ← C_neg, ← C_pow, ← C_mul, coeff_C_mul]
    simp
  rw [h_zero, h_star, h_first] at h_lim
  refine mul_left_cancel₀ (a := (-1) ^ (k + 1) * (r g).val.det)
    (by simp [GeneralLinearGroup.det_ne_zero]) ?_
  rw [add_tsub_cancel_right]
  linear_combination -h_lim

end ConjugateSelfDual

/-!
## Representations of a type under conjugate places, twists, and labelled eigenforms

How the property `New.Selmer.IsRepOfType` of an `ℓ`-adic Galois representation `R` arises and how it
is preserved.

* `New.Selmer.IsRepOfType.twist_avatar`: `IsRepOfType` is preserved, with shifted twist, jumps and
  labels, by twisting with the avatar of an algebraic Hecke character whose tame part is `1` off the
  chosen places.
-/

namespace New.Selmer

open NumberField IsCMField InfinitePlace Matrix Submodule Polynomial Fintype GaloisRep Period

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {P : Parameters} {D : Data P}
  {r n m : Type} [Fintype r] [DecidableEq r] [Fintype n] [Fintype m] [DecidableEq m]

omit [PadicIso ℓ] in
/-- If the trace form on the image of `R` is non-degenerate, so is that on the image of its dual
`R'`, `g ↦ (R g⁻¹)ᵀ`. -/
lemma isTraceNondeg_transpose_inv {R R' : GalRep ℓ D.E m} (h_nondeg : IsTraceNondeg R)
    (h_eq : ∀ g : AbsGal D, R' g = transposeGL (R g⁻¹)) : IsTraceNondeg R' := by
  intro x hx h_trace
  -- Transposition carries the span of the image of `R'` into that of `R`.
  have hx' : xᵀ ∈ span (PadicAlgCl ℓ) (Set.range fun g : AbsGal D ↦ (R g).val) :=
    span_mono (by simp [h_eq, -map_inv, Set.range_subset_iff])
      (apply_mem_span_image_of_mem_span (transposeLinearEquiv m m _ (PadicAlgCl ℓ)).toLinearMap hx)
  refine transpose_eq_zero.1 (h_nondeg _ hx' fun g ↦ ?_)
  simpa [h_eq, ← trace_transpose_mul x] using h_trace g⁻¹

/-- Composing a complex embedding `σ` with complex conjugation replaces each jump `u` of a weight
`κ` in rank `k` (`New.jumps`) by `k - 1 - u`. -/
lemma count_jumps_comp_star (κ : Weight D.E) (k : ℕ) (σ : D.E →+* ℂ) (u : ℤ) :
    (jumps κ k (σ.comp starRingAut.toRingHom)).count u =
      (jumps κ k σ).count (-u - -(k.pred : ℤ)) := by
  have h_conj : σ.comp starRingAut.toRingHom = ComplexEmbedding.conjugate σ :=
    Eq.symm (isConj_complexConj D.E σ)
  simp only [h_conj, jumps, Multiset.count_map, Nat.pred_eq_sub_one]
  congr! 2
  grind [Φ_mk_eq_or_star_eq, mk_conjugate_eq, Multiset.mem_range]

/-- Let `R` be conjugate dual with twist `1 - k` and of finite type at the conjugate `conjPlace A`
of the place `A`. Then (a) `R` is of finite type at `A`; (b) if `R` has the jumps of a weight `κ` in
rank `k` at the conjugate place, it has them at `A`; (c) a polynomial that kills an inertial `s` at
the conjugate place kills `conjGal s⁻¹` at `A`.

A case of the compatibility of Weil–Deligne representations and Hodge–Tate weights with duals and
conjugation (Fontaine). -/
theorem isFiniteTypeAt_and_hasJumpsAt_of_conjPlace {R : GalRep ℓ D.E m} {k : ℕ} {A : ClosurePlace}
    (h_dual : IsConjSelfDual k R) (h_fin : IsFiniteTypeAt R (conjPlace A)) :
    -- (a)
    IsFiniteTypeAt R A ∧
    -- (b)
    (∀ κ : Weight D.E, HasJumpsAt R (conjPlace A) (jumps κ k) → HasJumpsAt R A (jumps κ k)) ∧
    -- (c)
    ∀ s ∈ inertiaGroup Gal(Ω/D.E) (conjPlace A), ∀ Q : (PadicAlgCl ℓ)[X],
      PolyKillsAt R (conjPlace A) s Q → PolyKillsAt R A (conjGal s⁻¹) Q := by
  -- `R ∘ conjGal` is conjugate to the twisted dual `r'` of `R`, as both have a nondegenerate trace
  -- form and their traces agree. So it suffices to pass each local clause at the conjugate place
  -- from `R` to `r'`; above `ℓ` this uses the dot product, which pairs `r'` and `R` into a power
  -- of the cyclotomic character.
  let Rdual : GalRep ℓ D.E m := .mk' (fun g ↦ transposeGL (R g⁻¹)) (by simp [Units.ext_iff])
  let r' := twistByChar (cyclotomicCharIn _ Ω ℓ ^ k.pred)⁻¹ Rdual
  have h_nondeg : IsTraceNondeg r' :=
    (isTraceNondeg_transpose_inv (R' := Rdual) h_dual.nondeg fun g : AbsGal D ↦ rfl).twist _
  have h_normal : IsTraceNondeg (R.comp conjGal) :=
    h_dual.nondeg.comp conjGal ⟨fun _ _ _ ↦ ⟨_, conjGal_conjGal _⟩⟩
  obtain ⟨Pm, hPm⟩ : ∃ Pm : GL m (PadicAlgCl ℓ), ∀ g, (r' g).1 * Pm = Pm * (R (conjGal g)).1 :=
    h_nondeg.exists_conj_of_trace_eq _ (AlgHom.id (PadicAlgCl ℓ) (Matrix m m (PadicAlgCl ℓ)))
      h_normal.hasSemiprimeSpan
      (by simp [r', Rdual, h_dual.trace_conj, Units.smul_def, cyclotomicInv])
  -- The local clauses pass from `r'` at the conjugate place to `R` at `A`.
  obtain ⟨fin_of, jump_of, poly_of⟩ :
      (IsFiniteTypeAt r' (conjPlace A) → IsFiniteTypeAt R A) ∧
      (Pm.val * Pm.inv = 1 → ∀ {rel : ℕ → ℕ → Prop} {J : (D.E →+* ℂ) → Multiset ℤ},
        JumpsRelAt r' (conjPlace A) rel (fun σ : D.E →+* ℂ ↦ J (σ.comp starRingAut.toRingHom)) →
          JumpsRelAt R A rel J) ∧
      ∀ s ∈ Set.univ, ∀ {Q : (PadicAlgCl ℓ)[X]},
        PolyKillsAt r' (conjPlace A) s Q → PolyKillsAt R A (conjGal s) Q :=
    local_clauses_of_retract (A := A) cmConj starRingAut.toRingHom (by simp) (by simp [conjGal])
      (Homeomorph.mk ⟨_, _, conjGal_conjGal, conjGal_conjGal⟩).isOpenEmbedding Filter.univ_mem
      (fun g _ ↦ hPm g) Pm.inv_val
  -- Above `ℓ`, compare `r'` and `R` on the decomposition group through the pairing.
  let dot := dotProductEquiv (PadicAlgCl ℓ) m
  have h_pair [H : PadicPlaceEmbedding D.E (conjPlace A) ℓ]
      (g : decompGroup Gal(Ω/D.E) (conjPlace A)) (x y : m → PadicAlgCl ℓ) :
      dot (decompRep r' (conjPlace A) g x) (decompRep R (conjPlace A) g y) =
        (χ g ^ (-k.pred : ℤ)).1 • dot x y := by
    simp [dot, r', Rdual, H.cyclotomicGp_eq_cyclotomicChar, mulVec_transpose, ← dotProduct_mulVec,
      @Algebra.smul_def ℤ_[ℓ], Units.smul_def]
  have h_jump (H : PadicPlaceEmbedding D.E (conjPlace A) ℓ) (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ])
      (u : ℤ) :
      jump (decompRep r' (conjPlace A)) γ u = jump (decompRep R (conjPlace A)) γ (-u - -k.pred) :=
    jump_eq_of_pairing h_fin.2 dot _ h_pair
  have h_adm (H : PadicPlaceEmbedding D.E (conjPlace A) ℓ) :
      IsPotentiallyCrystalline (decompRep r' (conjPlace A)) ∧ ∀ {s Q}, IsWeilPair (H.toGp s) 0 →
        IsKilledBy (decompRep R (conjPlace A)) s 0 Q →
        IsKilledBy (decompRep r' (conjPlace A)) s⁻¹ 0 Q :=
    h_fin.2.of_pairing le_rfl _ dot h_pair
  refine ⟨fin_of ⟨fun hℓ ↦ ?_, @fun H ↦ (h_adm H).1⟩, fun κ h ↦ ?_, fun s hs Q h ↦ ?_⟩
  · -- Away from `ℓ` the cyclotomic character is trivial on inertia.
    filter_upwards [h_fin.1 hℓ] with s h_triv hs
    simp [r', Rdual, h_triv hs, cyclotomicChar_eq_one_of_mem_inertiaGroup ℓ hs hℓ, Units.ext_iff]
  · refine jump_of Pm.val_inv fun H γ τ hτ u ↦ ?_
    rw [h_jump H, ← h hτ]
    -- Conjugating the embedding replaces each jump `u` of the weight by `k - 1 - u`.
    exact count_jumps_comp_star κ k _ u
  · refine poly_of _ trivial ⟨fun hℓ ↦ ?_, @fun H _ n hn ↦ ?_⟩
    · -- Away from `ℓ`, `r' s⁻¹` is the transpose of `R s` for `s` in inertia.
      have h_transpose := congrArg transpose (h.1 hℓ)
      simpa [r', Rdual, cyclotomicChar_eq_one_of_mem_inertiaGroup ℓ hs hℓ, aeval_eq_sum_range,
        transpose_sum]
        using h_transpose
    · -- An inertial element has Weil degree `0`, so `n = 0`.
      cases (ℓ.pow_right_inj Fact.out).1
        (hn.eq_pow_of_isFrob (H.isWeilPair_zero_iff.2 (inv_mem hs)))
      apply (h_adm H).2 hn.inv (@h.2 H _ _ hn.inv)

/-- Let `φ : K →* L` be multiplicative and `u` a unit of `F`. The product of `X - φ x` over the
roots `x` of `p` in `K` divides `Q (φ u * X)`, where `Q` is the same product for the polynomial
whose roots are those of `p` times `u`. -/
lemma prod_aroots_dvd_prod_aroots_scaleRoots_comp {F K L : Type*} [Field F] [Field K] [Algebra F K]
    [CommRing L] (φ : K →* L) (p : F[X]) (u : Fˣ) :
    ((p.aroots K).map fun x : K ↦ X - C (φ x)).prod ∣
      (((p.scaleRoots u.val).aroots K).map fun x : K ↦ X - C (φ x)).prod.comp
        (C (φ (algebraMap F K u.val)) * X) := by
  have h_roots : (p.scaleRoots u.val).aroots K =
      (p.aroots K).map fun x : K ↦ algebraMap F K u.val * x := by
    obtain rfl | hp := eq_or_ne p 0
    · simp
    · rw [aroots, map_scaleRoots p u.val _ (by simpa using hp),
        roots_scaleRoots _ (u.isUnit.map (algebraMap F K)), aroots]
  rw [h_roots, multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  -- Factor by factor, `φ u * X - φ (u * x) = (X - φ x) * φ u`.
  refine Multiset.prod_dvd_prod_of_dvd _ _ fun x _ ↦ ⟨C (φ (algebraMap F K u.val)), ?_⟩
  simp only [Function.comp_apply, map_mul, sub_comp, mul_comp, X_comp, C_comp]
  ring

/-- Let the descent pair `O` with some polynomials `d` form a lift setting for `ϑ`, so that the
places `O.chosenPlace i` are chosen. Let `R` be a representation of a type: conjugate self-dual of
twist `1 - k`, with jumps `J` and level `S`, inertia at `O.chosenPlace i` acting through the roots
of a polynomial `c i` over the residue field. Let `a` be a character of `U(1)` of weight `e` whose
tame part `ψ` is `1` at every place that is not chosen (`D.IsChosen`). Twist `R` by the `ℓ`-adic
avatar of the algebraic Hecke character `ha.toAlgebraic k' j`,
`y ↦ a(y / ȳ) υ(y)^{-k'} |y|^{j - k'/2}` with `υ` the fixed splitting character. The result is a
representation of a type of level `S` and twist `1 - b`, where `(b - 1) + (2 * j - k') = k - 1` with
truncated subtractions `b - 1`, `k - 1`. Its jumps are shifted by minus the infinity type, and the
roots of `c i` are scaled by the unit of the residue field that names the character
`ψ (O.chosenPlace i)` (`New.charName`). -/
theorem IsRepOfType.twist_avatar {O : DescentPair D.E r n} {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} {R : GalRep ℓ D.E m} {k : ℕ}
    {S : Set (FinPlace D.E)} {J : (D.E →+* ℂ) → Multiset ℤ} {a : AutChar D.E}
    {e : InfinitePlace D.E → ℤ} {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} {b : ℕ}
    (hR : IsRepOfType O k J c S R) (ha : AutChar.HasWeight a e ψ) (k' j : ℤ)
    (hb : (b - 1 : ℕ) + (2 * j - k') = (k - 1 : ℕ))
    {d : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_setting : IsLiftSetting O d ϑ)
    (hψ_off : ∀ v : FinPlace D.E, ¬D.IsChosen v → ψ v = 1) :
    IsRepOfType O b
      (fun σ : D.E →+* ℂ ↦ (J σ).map fun u : ℤ ↦ u + -(ha.toAlgebraic k' j).infinityType σ)
      (fun i : O.ChosenIndex ↦
        (c i).scaleRoots
          (charName (faithfulChar (ResField (O.chosenPlace i))) (ψ (O.chosenPlace i))).val)
      S (twistByChar (ha.toAlgebraic k' j).avatar R) := by
  -- Let `μ` be the avatar of `θ`, and `μ₁` the same character read in `1 × 1` matrices. Each local
  -- clause passes to the twist `μ • R` from the clause for `R` and the clause for `μ₁`.
  let θ : AlgHeckeChar D.E := ha.toAlgebraic k' j
  let μ : Gal(Ω/D.E) →* (PadicAlgCl ℓ)ˣ := θ.avatar
  let μ₁ : GalRep ℓ D.E (Fin 1) := (GeneralLinearGroup.scalar (Fin 1)).comp μ
  have h_twist (g : Gal(Ω/D.E)) : (twistByChar μ R g).val = (μ g).val • (R g).val := rfl
  have h_dual : IsConjSelfDual b (twistByChar μ R) := by
    have h_cont : Continuous fun g : Gal(Ω/D.E) ↦ (μ g).val • (R g).val :=
      (Units.continuous_val.comp θ.continuous_avatar).smul
        (Units.continuous_val.comp hR.continuous)
    refine ⟨.of_coeHom_comp h_cont, hR.nondeg.twist μ, fun g ↦ ?_⟩
    -- The twist shifts the power of the cyclotomic character by `2 * j - k'`, as `hb` requires.
    have hμ_conj : μ (conjGal g) =
        cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ g ^ (2 * j - k') * (μ g)⁻¹ :=
      eq_mul_inv_of_mul_eq (avatar_conjGal_mul_avatar ha k' j g)
    have h_exp : 2 * j - k' = (k - 1 : ℕ) - (b - 1 : ℕ) := eq_sub_of_add_eq' hb
    have h_trace : (R (conjGal g)).val.trace =
        cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ (k - 1) * (R g⁻¹).val.trace := hR.trace_conj g
    simp [h_exp, h_trace, hμ_conj, zpow_sub₀, field, Units.smul_def, cyclotomicInv]
  refine { toIsConjSelfDual := h_dual, local_conditions v hv A hA := ?_, labelled i A := ?_ }
  · obtain ⟨hR_fin, hR_jumps, hR_good⟩ :
        IsFiniteTypeAt R A ∧ HasJumpsAt R A J ∧ (v ∉ placesAboveM D → IsGoodAt R A) :=
      hR.local_conditions v hv hA
    -- The avatar is of finite type at `A`, with one jump, minus the infinity type of `θ`.
    have h_compat : AvatarCompatAt v θ := avatarCompatAt_of_hasPrimitiveRoot5040 θ
    obtain ⟨hμ_fin : IsFiniteTypeAt μ₁ A,
        hμ_jumps : HasJumpsAt μ₁ A fun τ : D.E →+* ℂ ↦ {-θ.infinityType τ}, -⟩ := h_compat hA
    refine ⟨hR_fin.twist h_twist hμ_fin, hR_jumps.twist h_twist hμ_jumps, fun hv_off ↦ ?_⟩
    -- Off `p₀ p₁` neither `v` nor its conjugate is chosen, so `θ` is unramified at `v`.
    have hψ_v : ψ v = 1 := hψ_off v fun h_chosen ↦ hv_off h_chosen.mem_placesAboveM
    have hψ_star : ψ (star v) = 1 :=
      hψ_off (star v) fun h_chosen ↦ hv_off (star_mem_placesAboveM.1 h_chosen.mem_placesAboveM)
    have h_unr : CharUnramifiedAt θ.character v :=
      ha.charUnramifiedAt_toAlgebraic hψ_v hψ_star k' j
    obtain ⟨hμ_good : IsGoodAt μ₁ A, -⟩ := h_compat.isSphericalAbove_of_unramified h_unr hA
    exact (hR_good hv_off).twist h_twist hμ_good
  · -- Let `s` have tame exponent `y` at `A` over `w`, and let `u` be the label of `ψ w`.
    intro s y hy
    let w : FinPlace D.E := O.chosenPlace i
    let K : Type := AlgebraicClosure (ResField w)
    let T : MulChar K ℂ := faithfulChar (ResField w)
    let u : (ResField w)ˣ := charName T (ψ w)
    let φ : K →* PadicAlgCl ℓ := ιℓ.toMonoidHom.comp (T ^ y).toMonoidHom
    -- `s` acts on `μ` by `φ u`, and on `R` through the values of `φ` at the roots of `c i`.
    have hψ_star : ψ (star w) = 1 := hψ_off (star w) (h_setting.isChosen_chosenPlace i).not_star
    have hw_split : w.IsSplit := O.isConjApart_chosenPlace.star_ne i i
    have hμ_kill : PolyKillsAt μ₁ A s (X - C (φ (algebraMap (ResField w) K u.val))) := by
      simpa [μ₁, μ, θ, φ, u, T] using isLabelledAt_avatar ha k' j hψ_star hw_split hy
    have hR_kill : PolyKillsAt R A s (((c i).aroots K).map fun x : K ↦ X - C (φ x)).prod :=
      hR.labelled hy
    -- So it acts on `μ • R` through the values of `φ` at these roots times `u`.
    show PolyKillsAt (twistByChar μ R) A s
      ((((c i).scaleRoots u.val).aroots K).map fun x : K ↦ X - C (φ x)).prod
    exact (hR_kill.of_dvd (prod_aroots_dvd_prod_aroots_scaleRoots_comp φ (c i) u)).twist h_twist
      hμ_kill

/-- Let the descent pair `O` with some polynomials `d` form a lift setting for `ϑ`, so that the
places `O.chosenPlace i` are chosen. Let `f` be an eigenform of weight `κ` on the definite unitary
group of rank `card m`, and `R` attached to its Hecke polynomials `H`. Suppose that `f` is spherical
at every place that is off `S`, above `ℓ` or above `p₀ p₁`, except the chosen places of `O` and
their conjugates. Suppose also that the type of `f` at `O.chosenPlace i` is induced from the one
with label `c i`, a polynomial of degree `card r`, and trivial characters on blocks of sizes `t l`.
Then `R` is a representation of a type: conjugate self-dual of twist `1 - card m` and level `S`,
with the jumps of `κ`, inertia at `O.chosenPlace i` acting through the roots of
`c i * (X - 1) ^ (card m - card r)`. -/
theorem isRepOfType_of_hasProductLabel {O : DescentPair D.E r n} {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} {R : GalRep ℓ D.E m}
    {S : Set (FinPlace D.E)} {d : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]}
    (h_setting : IsLiftSetting O d ϑ) {κ : Weight D.E}
    {f : Gf D.E m → WeylIndex m κ.1 → ℂ} {s : ℕ} {H : FinPlace D.E → ℂ[X]}
    (hf : f ∈ (stdSpace D.E m).forms κ) (h_eigen : IsEigenform f H) (hR : Attached H R)
    (h_spherical : ∀ v ∉ S \ (placesDividing D.E ℓ ∪ placesAboveM D),
      v ∉ (Set.range O.chosenPlace).conjClosure →
        f ∈ sphericalAt (rightRegular ℂ (Gf D.E m) (WeylIndex m κ.1 → ℂ)) v)
    {t : Fin s → ℕ}
    (h_prod : ∀ i : O.ChosenIndex,
      HasProductLabel f (O.isConjApart_chosenPlace.star_ne i i)
        (faithfulChar (ResField (O.chosenPlace i))) (card r) (c i) 1 t)
    [Nonempty m] :
    IsRepOfType O (card m) (jumps κ (card m))
      (fun i : O.ChosenIndex ↦ c i * (X - 1) ^ (card m - card r)) S R := by
  -- At the places over `O.chosenPlace i`: finite type, jumps, and the action of inertia through the
  -- label.
  have h_lab (i : O.ChosenIndex) {A : ClosurePlace} (hA : IsPlaceOver A (O.chosenPlace i)) :
      IsFiniteTypeAt R A ∧ HasJumpsAt R A (jumps κ (card m)) ∧
        IsLabelledAt A (faithfulChar (ResField (O.chosenPlace i))) (card r).factorial
          (PolyKillsAt R A)
          (c i * ∏ l : Fin s, (X - C (charName (faithfulChar (ResField (O.chosenPlace i)))
            (1 : MulChar (ResField (O.chosenPlace i)) ℂ)).val) ^ t l) :=
    hR.isLabelledAt hf h_eigen (h_prod i) hA
  refine ⟨⟨isConjSelfDual_of_attached h_eigen hR, fun v hv A hA ↦ ?_⟩, fun i A s a hs ↦ ?_⟩
  · obtain ⟨i, rfl⟩ | ⟨i, hi⟩ | hv' :
        v ∈ Set.range O.chosenPlace ∨
        star v ∈ Set.range O.chosenPlace ∨
        v ∉ (Set.range O.chosenPlace).conjClosure := by grind
    · -- At a chosen place, which lies above `p₀` or `p₁`, the label gives the local clauses.
      obtain ⟨h_fin, h_jump, -⟩ := h_lab i hA
      have h_above : O.chosenPlace i ∈ placesAboveM D :=
        (h_setting.isChosen_chosenPlace i).mem_placesAboveM
      exact ⟨h_fin, h_jump, fun hg ↦ (hg h_above).elim⟩
    · -- At the conjugate of a chosen place, `isFiniteTypeAt_and_hasJumpsAt_of_conjPlace` carries
      -- them over.
      have hA' : IsPlaceOver (conjPlace A) (O.chosenPlace i) := by
        simpa [hi] using hA.conjPlace_star
      obtain ⟨h_fin, h_jump, -⟩ := h_lab i hA'
      obtain ⟨h_fin', h_jump', -⟩ :=
        isFiniteTypeAt_and_hasJumpsAt_of_conjPlace (isConjSelfDual_of_attached h_eigen hR) h_fin
      have h_above : v ∈ placesAboveM D := by
        simpa [hi] using (h_setting.isChosen_chosenPlace i).mem_placesAboveM
      exact ⟨h_fin', h_jump' κ h_jump, fun hg ↦ (hg h_above).elim⟩
    · -- Elsewhere the form is spherical, and local-global compatibility `sphericalCompat_std`
      -- applies.
      obtain ⟨h_unr, h_jump, -⟩ :=
        (sphericalCompat_std v hf h_eigen).2 hR (h_spherical v hv hv') A hA
      exact ⟨(isGoodAt_iff.1 h_unr).1, h_jump, fun _ ↦ h_unr⟩
  · -- The completing characters are trivial, and their exponents add up to `card m - card r`.
    obtain ⟨-, -, h_kill⟩ := h_lab i hs.1
    obtain ⟨-, -, h_sum, -⟩ := h_prod i
    have h_label :
        c i * (X - 1) ^ (card m - card r) =
          c i * ∏ l, (X - C (charName (faithfulChar (ResField (O.chosenPlace i)))
            (1 : MulChar (ResField (O.chosenPlace i)) ℂ)).val) ^ t l := by
      simp [Finset.prod_pow_eq_pow_sum, ← h_sum]
    rw [h_label]
    exact h_kill hs

end New.Selmer

end
