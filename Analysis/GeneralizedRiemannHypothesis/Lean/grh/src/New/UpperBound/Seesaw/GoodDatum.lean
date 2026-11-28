import New.UpperBound.Seesaw.AdmissibleEvaluation
import New.UpperBound.Seesaw.LevelIdeles
import New.UpperBound.Size.ShortColumns

/-!
# Evaluated data as admissible combinations of glued translates of the vacuum

The data `pointDatumY ϑ k` of the chain of spaces `D.spaceY k`, moved by elements that are integral
away from the level of the twist, are admissible combinations of translates of the vacuum. The
tensor of their evaluations is an admissible combination of the glued translates
`New.Data.gluedVacuum` (`New.Data.exists_isAdmissibleCombination_gluedVacuum`).

Notions from other files:

* `V.finHeisenbergOp x V.vacElem`: the translate of the vacuum of the space `V` by the finite adelic
  vector `x`, in the space `𝒮 V` of the Weil representation `V.ω`.
* `translations ι q d`, `weightedTranslations q d`: the finite adelic vectors `x` such that `d x`
  (respectively each `d i * x i`) is integral at the places not dividing `q`.
* `IsAdmissibleCombination v A q d p B z`: `z` is a finite combination of the `v x` with `x ∈ A`,
  whose coefficients times `d` are integral away from `q` and, if `p` holds, have absolute sum at
  most `B` under every automorphism of `ℂ`.
* `localLevel n S`: the elements of the finite adelic unitary group `Gf E n` that are integral at
  the places of `S`.
* `D.piM`: the integer `π̄₀ π̄₁` of `E`, whose prime divisors are the chosen places.
* An edge of the chain is an arrow `D.spaceY k → D.spaceY (k + 1)`; the pair of edges number `i`
  consists of the arrows from `2 i` to `2 i + 1` and from `2 i + 1` to `2 i + 2`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

/-! ## Scaling factors and the evaluation of a pair of edges -/

namespace New.Data

open TensorProduct Seesaw Prod Space Ideal Weil Matrix Grading Finset Modulus TensorChain
open scoped NumberField

variable {P : Parameters} (D : Data P)

/-- The quotient `c / c̄` of the finite idele `c = D.chosenIdele`, which generates the ideal of
`D.piM`, by its conjugate. -/
noncomputable def chosenRatio : 𝔸f D.E := star (↑D.chosenIdele⁻¹ : 𝔸f D.E) * D.chosenIdele

/-- The adele `D.chosenRatio = c / c̄` has norm one. -/
lemma chosenRatio_mul_star : D.chosenRatio * star D.chosenRatio = 1 :=
  calc D.chosenRatio * star D.chosenRatio
    _ = D.chosenIdele * ↑D.chosenIdele⁻¹ * star (D.chosenIdele * ↑D.chosenIdele⁻¹ : 𝔸f D.E) := by
      simp only [chosenRatio, star_mul', star_star]
      ring
    _ = 1 := by rw [Units.mul_inv, star_one, mul_one]

/-- The adele `D.chosenRatio = c / c̄` has component `1` at every place above the prime `D.N`. -/
lemma chosenRatio_apply_of_N_mem {w : FinPlace D.E} (hw : ↑D.N ∈ w.asIdeal) :
    D.chosenRatio w = 1 := by
  obtain ⟨h_self, h_conj⟩ : ¬D.IsChosen w ∧ ¬D.IsChosen (star w) := D.not_isChosen_of_N_mem hw
  simp [chosenRatio, idele_inv_apply_and_ne_zero, D.chosenIdele_apply_of_not_isChosen, h_self,
    h_conj]

/-- The integer `D.piM`, whose prime divisors are the chosen places, is a unit at the places
above the prime `D.N`. -/
lemma v_piM_eq_one_of_N_mem {w : FinPlace D.E} (hw : ↑D.N ∈ w.asIdeal) :
    Valued.v ((algebraMap (𝓞 D.E) (Ô D.E) D.piM : 𝔸f D.E) w) = 1 := by
  rw [← v_chosenIdele, D.chosenIdele_apply_of_not_isChosen (D.not_isChosen_of_N_mem hw).1, map_one]

/-- For `β = D.piM` and `δ = D.chosenRatio`, the adeles `β̄ δ` and `β` have the same valuation
at every finite place: `δ = c / c̄` for an idele `c` with the valuations of `β`. -/
lemma v_star_piM_mul_chosenRatio (w : FinPlace D.E) :
    Valued.v ((star (algebraMap (𝓞 D.E) (Ô D.E) D.piM : 𝔸f D.E) * D.chosenRatio) w) =
      Valued.v ((algebraMap (𝓞 D.E) (Ô D.E) D.piM : 𝔸f D.E) w) := by
  let β : 𝔸f D.E := algebraMap (𝓞 D.E) (Ô D.E) D.piM
  have hβ (u : FinPlace D.E) : Valued.v (β u) = Valued.v ((D.chosenIdele : 𝔸f D.E) u) :=
    (D.v_chosenIdele u).symm
  have h_conj : Valued.v ((star β * star (↑D.chosenIdele⁻¹ : 𝔸f D.E)) w) = 1 := by
    simp [hβ, idele_inv_apply_and_ne_zero]
  calc Valued.v ((star β * D.chosenRatio) w)
    _ = Valued.v ((star β * star (↑D.chosenIdele⁻¹ : 𝔸f D.E)) w) *
          Valued.v ((D.chosenIdele : 𝔸f D.E) w) := by
      rw [chosenRatio, ← mul_assoc, finAdele_mul_apply, map_mul]
    _ = Valued.v (β w) := by rw [h_conj, one_mul, hβ]

/-- Let `η = normNegOne` be the chosen unit of norm `-1`, `α` the idele of the Weil data and
`c = D.chosenIdele`. The idele `flipScale = η̄ ᾱ / α` times `a / ā`, for `a = D.ideleA = α / c̄`,
is `η̄` times `D.chosenRatio = c / c̄`. -/
lemma flipScale_mul_divStar_ideleA :
    (flipScale D.E : 𝔸f D.E) * divStar D.ideleA =
      star (normNegOne (E := D.E) : 𝔸f D.E) * D.chosenRatio := by
  -- The factors `α` and `ᾱ` cancel.
  have h_units : star WeilData.α * WeilData.α⁻¹ * (D.ideleA * star D.ideleA⁻¹) =
      star D.chosenIdele⁻¹ * D.chosenIdele := by
    simp [ideleA, div_eq_mul_inv, star_mul', mul_comm, mul_left_comm]
  have h_adeles : (↑(star WeilData.α * WeilData.α⁻¹ : (𝔸f D.E)ˣ) : 𝔸f D.E) * divStar D.ideleA =
      D.chosenRatio := by
    rw [coe_divStar, ← Units.coe_star, ← Units.val_mul, ← Units.val_mul, h_units, Units.val_mul,
      Units.coe_star, chosenRatio]
  rw [coe_flipScale, mul_assoc, h_adeles]

variable {X X'' : Type}

/-- Let `β = D.piM` and `δ = D.chosenRatio`, and let `κ` be factors on the rows
`PairIndex X X''`, each equal to `1` or `δ` and equal to `1` on the first block. Then `κ` is a
scaling (`IsScalingAtM`): `δ` has norm one and is `1` above `D.N`, where `β` is a unit, and the
factors become integral after multiplication by `β̄`, those of the first block also by `β`. -/
lemma isScalingAtM_of_eq_one_or_eq {κ : PairIndex X X'' → 𝔸f D.E}
    (hκ : ∀ b : PairIndex X X'', κ b = 1 ∨ κ b = D.chosenRatio)
    (hκ_inl : ∀ a : X ⊕ Unit, κ (.inl a) = 1) :
    IsScalingAtM D.N (algebraMap (𝓞 D.E) (Ô D.E) D.piM) D.chosenRatio κ := by
  let β : Ô D.E := algebraMap (𝓞 D.E) (Ô D.E) D.piM
  have hβ : (β : 𝔸f D.E) ∈ Ô D.E := SetLike.coe_mem β
  have h_star (b : PairIndex X X'') : star (β : 𝔸f D.E) * κ b ∈ Ô D.E := by
    rcases hκ b with h_one | h_ratio
    · simpa only [h_one, mul_one] using star_mem_Ô hβ
    · rw [h_ratio]
      exact mem_Ô.2 fun w ↦ (D.v_star_piM_mul_chosenRatio w).trans_le (mem_Ô.1 hβ w)
  have h_selfOrConj : ∀ b : PairIndex X X'', selfOrConj β b * κ b ∈ Ô D.E := by
    rintro (a | b)
    · simp [selfOrConj, hκ_inl]
    · simpa [selfOrConj] using h_star (.inr b)
  exact
    { mul_star_self_eq_one := D.chosenRatio_mul_star
      apply_eq_one := fun _ ↦ D.chosenRatio_apply_of_N_mem
      v_eq_one := fun _ ↦ D.v_piM_eq_one_of_N_mem
      eq_one_or_eq := hκ
      star_mul_mem := h_star
      selfOrConj_mul_mem := h_selfOrConj }

/-- The scaling of a pair of edges other than the last: the factors `1` on all rows
`PairIndex X X''` form a scaling for `β = D.piM` and `δ = D.chosenRatio`
(see `isScalingAtM_of_eq_one_or_eq`). -/
lemma isScalingAtM_one :
    IsScalingAtM D.N (algebraMap (𝓞 D.E) (Ô D.E) D.piM) D.chosenRatio
      (1 : PairIndex X X'' → 𝔸f D.E) :=
  D.isScalingAtM_of_eq_one_or_eq (fun _ ↦ Or.inl rfl) fun _ ↦ rfl

/-- The scaling of the last pair of edges: the factors `lastScaling`, equal to `δ` at the last row
and to `1` elsewhere, form a scaling for `β = D.piM` and `δ = D.chosenRatio`. -/
lemma isScalingAtM_lastScaling :
    IsScalingAtM D.N (algebraMap (𝓞 D.E) (Ô D.E) D.piM) D.chosenRatio
      (lastScaling X X'' D.chosenRatio) := by
  refine D.isScalingAtM_of_eq_one_or_eq ?_ fun a ↦ by simp [lastScaling]
  rintro (a | b | c) <;> simp [lastScaling]

/-- The norm-one adele `D.latticeScale j = (a / ā) ^ ⌈(m - j) / 2⌉`, where `a = D.ideleA` and
`m = 2 ϱ + 2` is the length of the chain, gains one factor `a / ā` from `j = 2 i + 2` to `j = 2 i`
when `i ≤ ϱ`. -/
lemma latticeScale_two_mul {i : ℕ} (hi : i ≤ D.ϱ) :
    D.latticeScale (2 * i) = divStar D.ideleA * D.latticeScale (2 * i + 2) := by
  have h_m : D.m = 2 * D.ϱ + 2 := D.m_eq_two_mul_varrho_add_two
  have h_exp : (D.m - 2 * i + 1) / 2 = (D.m - (2 * i + 2) + 1) / 2 + 1 := by lia
  rw [latticeScale, latticeScale, h_exp, pow_succ']

/-- The chain of hermitian spaces `Y j = D.spaceY j` ends at `j = D.m = 2 ϱ + 2`, where `ϱ = D.ϱ`.
For `i ≤ ϱ`, `D.doubleLiftEvalY i` is the map, attached to the arrows
`Y (2 i) → Y (2 i + 1) → Y (2 i + 2)`, from data on `Hom(Y (2 i + 1), (Y (2 i))⁻ ⊕ Y (2 i + 2))` to
tensors of finite data on `Hom(X (2 i), X (2 i + 1))` and `Hom(X (2 i + 1), X (2 i + 2))`, for the
standard definite spaces with basis `X j = D.X j`. Let `β = D.piM`. There is a constant `C` such
that, for every `n` prime to the prime `D.N`, this map sends the translate of the vacuum by a matrix
that is integral away from `n` after multiplication by `β` on the rows of `Y (2 i)` and by `β̄` on
those of `Y (2 i + 2)` to a finite combination of the vectors
`C • gluedTranslate D.N D.piNPlaces (t₁, t₂)` with `β̄ t₁`, `β̄ t₂` integral away from `n`. The
coefficients are integral away from `n` after multiplication by the number of integral matrices
modulo `β` of shape `(X (2 i) ⊕ X (2 i + 2)) × X (2 i + 1)`, and the absolute sum of their images
under any automorphism of `ℂ` is at most `1`. Here `gluedTranslate` is the sum, over vectors with
simple poles at the places `D.piNPlaces` dividing `π = D.piN` (where `π π̄ = D.N`), of translates of
the tensor of the two vacua moved by `t₁` and `t₂`. -/
lemma isAdmissibleEval_doubleLiftEvalY (i : ℕ) (hi : i ≤ D.ϱ) :
    IsAdmissibleEval D.N D.piNPlaces (algebraMap (𝓞 D.E) (Ô D.E) D.piM) (D.doubleLiftEvalY i)
      (selfOrConj (algebraMap (𝓞 D.E) (Ô D.E) D.piM)) := by
  -- Apply `isAdmissibleEval_finEval` to the middle pair (`i < ϱ`) or the last pair (`i = ϱ`).
  have h_scale : (flipScale D.E : 𝔸f D.E) * D.latticeScale (2 * i) =
      star (normNegOne (E := D.E) : 𝔸f D.E) * D.chosenRatio * D.latticeScale (2 * i + 2) := by
    rw [D.latticeScale_two_mul hi, Submonoid.coe_mul, ← mul_assoc, D.flipScale_mul_divStar_ideleA]
  unfold doubleLiftEvalY
  split_ifs with h_middle h_last
  · apply isAdmissibleEval_finEval (hP := D.isSplitLevel_piNPlaces) (hκ := D.isScalingAtM_one)
      (hπ := D.isSplitSquarefree_piNIdele) (hL := D.spansLattice_gradingY (2 * i + 1) _)
    · apply liftsNeighbours_middleDoubleLift (h_scale := h_scale) <;> apply D.spansLattice_gradingY
    · apply matchesDenominators_middleDoubleLift
  · -- The last space is standard (an instance argument of `liftsNeighbours_lastDoubleLift`), and
    -- its factor `latticeScale` is `1`.
    subst h_last
    have h_std : (D.spaceY (2 * D.ϱ + 2)).IsStd := by
      rw [← D.m_eq_two_mul_varrho_add_two]
      exact D.isStd_spaceY_last
    have h_one : D.latticeScale (2 * D.ϱ + 2) = 1 := by
      simp [latticeScale, D.m_eq_two_mul_varrho_add_two]
    rw [h_one, OneMemClass.coe_one, mul_one] at h_scale
    apply isAdmissibleEval_finEval (hP := D.isSplitLevel_piNPlaces)
      (hκ := D.isScalingAtM_lastScaling) (hπ := D.isSplitSquarefree_piNIdele)
      (hL := D.spansLattice_gradingY (2 * D.ϱ + 1) _)
    · -- `D.piNIdele` is by definition the principal idele of `π`.
      apply liftsNeighbours_lastDoubleLift (hπ := rfl) (h_scale := h_scale)
      exact D.spansLattice_gradingY (2 * D.ϱ) _
    · apply matchesDenominators_lastDoubleLift (hδ := D.v_star_piM_mul_chosenRatio)
  · lia

end New.Data

/-! ## The Weil action and products of translates of the vacuum -/

namespace New.Seesaw

open Matrix Space Weil Valued

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {q : ℕ} {g : Gf E n}
  {d : 𝔸f E} {x : n → 𝔸f E}

/-- An element `g` of the finite adelic unitary group that is integral away from `q` preserves the
group of vectors `x` with `d x` integral away from `q`. -/
lemma mulVec_mem_translations (hg : g ∈ localLevel n {w : FinPlace E | ↑q ∉ w.asIdeal})
    (hx : x ∈ translations n q d) : (g : Matrix n n (𝔸f E)) *ᵥ x ∈ translations n q d := by
  let M : Matrix n n (𝔸f E) := g
  have h_cols : M *ᵥ x = ∑ j : n, fun i : n ↦ M i j * x j :=
    funext fun i ↦ by rw [Finset.sum_apply, mulVec, dotProduct]
  rw [h_cols]
  refine sum_mem fun j _ i w hw ↦ ?_
  calc v ((d * (M i j * x j)) w)
    _ = v (M i j w) * v ((d * x j) w) := by rw [mul_left_comm, finAdele_mul_apply, map_mul]
    _ ≤ 1 := mul_le_one' ((hg w hw).isIntMatrix i j) (hx j w hw)

omit [Fintype n] [DecidableEq n] in
/-- If `d` is an integral adele and `x` lies in the standard lattice of integral vectors, then
`d x` is integral away from `q`. -/
lemma mem_translations_of_mem_stdLattice (hd : d ∈ Ô E) (hx : x ∈ stdLattice E n) :
    x ∈ translations n q d :=
  fun i w _ ↦ mem_Ô.1 (mul_mem hd (hx i)) w

variable [WeilData E]

/-- Let `g` in the finite adelic unitary group `Gf E n` be integral away from `q`, let `d` be an
integral adele, and let `d x` be integral away from `q`. Then `V.ω (1, g)`, with archimedean
component `1`, takes the translate of the vacuum by `x` to a finite combination of translates by
vectors `y` with `d y` integral away from `q`. The coefficients are integral away from `q`. If `p`
holds, which forces `q = 1`, the absolute sum of their images under any automorphism of `ℂ` is at
most `1`. -/
lemma isAdmissibleCombination_weil_of_mem_localLevel {s : n → ℤˣ} (V : Space E n s) {p : Prop}
    (hg : g ∈ localLevel n {w : FinPlace E | ↑q ∉ w.asIdeal}) (hd : d ∈ Ô E)
    (hx : x ∈ translations n q d) (hp : p → q = 1) :
    IsAdmissibleCombination (fun y : n → 𝔸f E ↦ V.finHeisenbergOp y V.vacElem) (translations n q d)
      q 1 p 1 (V.ω (1, g) (V.finHeisenbergOp x V.vacElem)) := by
  have h_mem (z : n → 𝔸f E) (hz : z ∈ stdLattice E n) :
      (g : Matrix n n (𝔸f E)) *ᵥ (x + z) ∈ translations n q d :=
    mulVec_mem_translations hg (add_mem hx (mem_translations_of_mem_stdLattice hd hz))
  -- The coefficients are roots of unity times `(finMultiplier g⁻¹)⁻¹`, a unit away from `q`.
  have h_coeff : finMultiplier g / (‖finMultiplier g‖ : ℂ) ^ 2 = (finMultiplier g⁻¹)⁻¹ := by
    rw [finMultiplier_inv, ← Complex.mul_conj', div_mul_cancel_left₀ (finMultiplier_ne_zero g)]
  have h_int :
      ((1 : ℕ) : ℂ) * (finMultiplier g / (‖finMultiplier g‖ : ℂ) ^ 2) ∈ integralAway q := by
    intro l _ hl ι
    rw [Nat.cast_one, one_mul, h_coeff, map_inv₀, norm_inv, Parameters.norm_finMultiplier_eq_one
      (localLevel_le_integralAbove_of_coprime hl (inv_mem hg)), inv_one]
  -- If `q = 1` then `g` is integral at all places, so its multiplier is `1`.
  have h_size (h_p : p) (σ : ℂ ≃+* ℂ) : ‖σ (finMultiplier g)‖ ≤ 1 := by
    have hg_int : g ∈ stdLevel E n :=
      mem_stdLevel_iff.2 fun w ↦ hg w (by simp [hp h_p, Ideal.one_notMem])
    simp [finMultiplier_eq_one_of_mem hg_int]
  simpa only [one_smul] using
    isAdmissibleCombination_weil_vacElem V (mul_one (finMultiplier g)) h_mem h_int h_size

/-- The product `arrowProduct` of the translates by `t₁` and `t₂` of the vacua of
`Hom(V, V')` and `Hom(V', V'')` is a root of unity times a translate of the vacuum of
`Hom(V', V⁻ ⊕ V'')`, where `V⁻ ⊕ V''` is `flipSum V V''`. If `star β` times each of the two
translations is integral away from `q`, then the joined translation `z` becomes integral away from
`q` after multiplication by `β` on the block of `V⁻` and by `star β` on the block of `V''`
(`selfOrConj β`). -/
lemma exists_arrowProduct_eq_smul_finHeisenbergOp {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
    {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}
    (V : Space E ι ε) (V' : Space E ι' ε') (V'' : Space E ι'' ε'') {β : Ô E} {t₁ : ι' × ι → 𝔸f E}
    {t₂ : ι'' × ι' → 𝔸f E} (ht₁ : t₁ ∈ translations (ι' × ι) q (star (β : 𝔸f E)))
    (ht₂ : t₂ ∈ translations (ι'' × ι') q (star (β : 𝔸f E))) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      ∃ z ∈ weightedTranslations q fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1,
        arrowProduct ((V.hom V').finHeisenbergOp t₁ (V.hom V').vacElem)
            ((V'.hom V'').finHeisenbergOp t₂ (V'.hom V'').vacElem) =
          ζ • (V'.hom (flipSum V V'')).finHeisenbergOp z (V'.hom (flipSum V V'')).vacElem := by
  -- The first block of `z` is `-c` times the adjoint of `t₁`, where `c` has norm `-1`; the second
  -- block is `t₂`.
  let c : 𝔸f E := normNegOne (E := E)
  let z : (ι ⊕ ι'') × ι' → 𝔸f E := fun
    | (.inl a, l) => -c * star (t₁ (l, a))
    | (.inr b, l) => t₂ (b, l)
  have hz_mem : z ∈ weightedTranslations q fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1 := by
    rintro ⟨a | b, l⟩
    · have hc_mem : -c ∈ Ô E := neg_mem (SetLike.coe_mem (normNegOne (E := E) : Ô E))
      simpa [selfOrConj, z] using star_mem_weightedTranslations hc_mem ht₁ id (l, a)
    · simpa [selfOrConj, z] using ht₂ (b, l)
  have hz_source : (fun i : ι' × ι ↦ c * star (z (.inl i.2, i.1))) = t₁ := by
    funext i
    calc c * star (-c * star (t₁ i)) = -(star c * c) * t₁ i := by
          rw [star_mul', star_neg, star_star]
          ring
      _ = t₁ i := by rw [star_normNegOne_mul_self, neg_neg, one_mul]
  let ζ : ℂ := stdLattice.semichar (fun i : ι' × ι ↦ z (.inl i.2, i.1)) ^ 2
  have hζ : IsOfFinOrder ζ := (stdLattice.isOfFinOrder_semichar _).pow
  have h_split : (V'.hom (flipSum V V'')).finHeisenbergOp z (V'.hom (flipSum V V'')).vacElem =
      ζ • arrowProduct ((V.hom V').finHeisenbergOp t₁ (V.hom V').vacElem)
        ((V'.hom V'').finHeisenbergOp t₂ (V'.hom V'').vacElem) := by
    rw [← arrowProduct_vacElem, finHeisenbergOp_arrowProduct, hz_source]
  refine ⟨ζ⁻¹, invMonoidHom.isOfFinOrder hζ, z, hz_mem, ?_⟩
  rw [h_split, inv_smul_smul₀ hζ.isUnit.ne_zero]

end New.Seesaw

namespace New.Data

open NumberField TensorProduct Seesaw Space Ideal Matrix Finset TensorChain

variable {P : Parameters} (D : Data P)

/-- Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part supported on the finite set of places
`ϑ.Q`. The modulus `D.twistModulus ϑ 1`, the product of the chosen places and of the places of
`ϑ.Q`, divides `D.piM` times the product `ϑ.normQ` of the norms of the places of `ϑ.Q`. -/
lemma piM_mul_normQ_mem_ideal (ϑ : D.TameChar) :
    D.piM * (ϑ.normQ : 𝓞 D.E) ∈ (D.twistModulus ϑ 1).ideal := by
  have h_twist : (ϑ.normQ : 𝓞 D.E) ∈ ∏ w : ϑ.Q, (w : FinPlace D.E).asIdeal := by
    rw [Nat.cast_prod, prod_coe_sort ϑ.Q fun w ↦ w.asIdeal]
    exact prod_mem_prod fun w _ ↦ absNorm_mem w.asIdeal
  have h_ideal : (D.twistModulus ϑ 1).ideal =
      (∏ i : (i : Fin 2) × D.ChosenPlace i, (D.chosenPlace i).asIdeal) ^ 1 *
        ∏ w : ϑ.Q, (w : FinPlace D.E).asIdeal := rfl
  rw [h_ideal, pow_one, ← Rows.span_piM D]
  exact mul_mem_mul (mem_span_singleton_self _) h_twist

/-- Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part supported on the finite set of places
`ϑ.Q`, and let `q = ϑ.normQ` be the product of the norms of these places. Let `Y k = D.spaceY k` be
the hermitian spaces of the chain, with bases `D.Y k ⊆ D.Y (k + 1)`. The datum `pointDatumY ϑ k` on
`Hom(Y k, Y (k + 1))` is the indicator of the matrix of this inclusion modulo the product of the
prime divisors of `D.piM` and the places of `ϑ.Q`, and the vacuum at the other finite places. It is
a finite combination of Heisenberg translates of the vacuum by adelic matrices `x` with
`star D.piM * x` integral away from `q`. The coefficients become integral away from `q` after
multiplication by the number of matrices modulo `D.piM`, and the absolute sum of their images under
any automorphism of `ℂ` is at most `1`, so this bound holds whatever the proposition `p` under which
it is asked for. -/
lemma isAdmissibleCombination_pointDatumY (ϑ : D.TameChar) (k : ℕ) (p : Prop) :
    IsAdmissibleCombination
      (fun x : D.Y (k + 1) × D.Y k → 𝔸f D.E ↦
        ((D.spaceY k).hom (D.spaceY (k + 1))).finHeisenbergOp x
          (vacElem ((D.spaceY k).hom (D.spaceY (k + 1)))))
      (translations (D.Y (k + 1) × D.Y k) ϑ.normQ (star (D.piM : 𝔸f D.E))) ϑ.normQ
      (absNorm (span {D.piM}) ^ Fintype.card (D.Y (k + 1) × D.Y k)) p 1
      (pointDatumY ϑ k : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1)))) := by
  -- The datum is the Schrödinger operator of the indicator `Ψ` of the class `M` of the inclusion
  -- matrix, applied to the vacuum.
  let R : Type := (D.twistModulus ϑ 1).ResidueRing
  let M : Matrix (D.Y (k + 1)) (D.Y k) R := inclMatrix _ (D.inclY k)
  let Ψ : (D.Y (k + 1) × D.Y k → R) → ℂ := Pi.single M 1 ∘ vecToMatrix
  have hΨ_zero (x : D.Y (k + 1) × D.Y k → R) (hx : x ≠ matrixToVec M) : Ψ x = 0 :=
    Pi.single_eq_of_ne (fun h : vecToMatrix x = M ↦ hx (congrArg matrixToVec h)) 1
  have hΨ_size (σ : ℂ ≃+* ℂ) : ∑ x, ‖σ (Ψ x)‖ ≤ 1 := by
    rw [Fintype.sum_eq_single (matrixToVec M) fun x hx ↦ by simp [hΨ_zero x hx]]
    simp [Ψ]
  have h_datum : (pointDatumY ϑ k : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1)))) =
      ((D.spaceY k).hom (D.spaceY (k + 1))).schrodingerOp (D.twistModulus ϑ 1).places
        ((D.twistModulus ϑ 1).liftFn Ψ)
        (vacElem _) := rfl
  rw [h_datum]
  exact isAdmissibleCombination_schrodingerOp _ _ (D.piM_mul_normQ_mem_ideal ϑ)
    (fun x ↦ by simp [Ψ, Pi.single_apply, ite_mem]) (fun _ ↦ hΨ_size) (projOn_vacElem _)

/-- Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part supported on the finite set of places
`ϑ.Q`, and let `q = ϑ.normQ` be the product of the norms of these places. Let every finite adelic
point `y k` of the unitary group of `Y k = D.spaceY k` be integral away from `q`. The datum
`pointDatumY ϑ k` on `Hom(Y k, Y (k + 1))`, moved by `(y k, y (k + 1))` under the Weil
representation, is a finite combination of Heisenberg translates of the vacuum by matrices `x` with
`star D.piM * x` integral away from `q`. The coefficients become integral away from `q` after
multiplication by the number of matrices modulo `D.piM`, and if `ϑ.Q` is empty the absolute sum of
their images under any automorphism of `ℂ` is at most `1`. -/
lemma isAdmissibleCombination_translatedPointDatumY (ϑ : D.TameChar) {y : ∀ k : ℕ, Gf D.E (D.Y k)}
    (hy : ∀ k : ℕ, y k ∈ localLevel (D.Y k) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) (k : ℕ) :
    IsAdmissibleCombination
      (fun x : D.Y (k + 1) × D.Y k → 𝔸f D.E ↦
        ((D.spaceY k).hom (D.spaceY (k + 1))).finHeisenbergOp x
          (vacElem ((D.spaceY k).hom (D.spaceY (k + 1)))))
      (translations (D.Y (k + 1) × D.Y k) ϑ.normQ (star (D.piM : 𝔸f D.E))) ϑ.normQ
      (absNorm (span {D.piM}) ^ Fintype.card (D.Y (k + 1) × D.Y k)) (ϑ.Q = ∅) 1
      (translatedPointDatumY ϑ y k : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1)))) := by
  -- The pair `(y k, y (k + 1))` acts as a character value `c` times the Weil action of one element
  -- `g` of the finite unitary group of the space of maps.
  let V : Space D.E (D.Y (k + 1) × D.Y k) (homSigns (D.signsY k) (D.signsY (k + 1))) :=
    (D.spaceY k).hom (D.spaceY (k + 1))
  let pair : New.G D.E (D.signsY k) × New.G D.E (D.signsY (k + 1)) := ((1, y k), (1, y (k + 1)))
  let g : Gf D.E (D.Y (k + 1) × D.Y k) := (G.onHom pair).2
  let c : ℂ := pairChar (rankTwist (D.chainChar ϑ (k + 1)) (D.Y k))
    (rankTwist (D.chainChar ϑ (k + 1)) (D.Y (k + 1))) pair
  have h_act : (translatedPointDatumY ϑ y k : 𝒮 V) = c • V.ω (1, g) (pointDatumY ϑ k) := by
    rw [← G.onHom_fin]
    rfl
  have hg : g ∈ localLevel _ {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal} :=
    fun w hw ↦ G.onHom_atPlace_mem (hy k w hw) (hy (k + 1) w hw)
  -- The number `c` is a quotient of values, at the determinants of `y (k + 1)` and `y k`, of
  -- characters that have a weight.
  have hc_int : c ∈ integralAway ϑ.normQ := fun l _ hl ι ↦ by
    simp [c, pair, D.hasWeight_liftChar.hasWeight_rankTwist.norm_apply_detFin_eq_one,
      localLevel_le_integralAbove_of_coprime hl (hy _)]
  have hc_size (σ : ℂ ≃+* ℂ) : ‖σ c‖ ≤ 1 := by
    simp [c, pair, D.hasWeight_liftChar.hasWeight_rankTwist.norm_map_eq_one, funext_iff]
  -- Expand the datum in translates of the vacuum and move each translate by `g`.
  let A : AddSubgroup (D.Y (k + 1) × D.Y k → 𝔸f D.E) :=
    translations _ ϑ.normQ (star (D.piM : 𝔸f D.E))
  have h_term (x : D.Y (k + 1) × D.Y k → 𝔸f D.E) (hx : x ∈ A) :
      IsAdmissibleCombination (fun z ↦ V.finHeisenbergOp z V.vacElem) A ϑ.normQ 1 (ϑ.Q = ∅) 1
        (V.ω (1, g) (V.finHeisenbergOp x V.vacElem)) :=
    isAdmissibleCombination_weil_of_mem_localLevel V hg (star_mem_Ô (coe_mem_Ô _)) hx
      fun hQ ↦ by simp [hQ]
  have h_moved : IsAdmissibleCombination (fun z ↦ V.finHeisenbergOp z V.vacElem) A ϑ.normQ
      (absNorm (span {D.piM}) ^ Fintype.card (D.Y (k + 1) × D.Y k)) (ϑ.Q = ∅) 1
      (V.ω (1, g) (pointDatumY ϑ k)) :=
    ((D.isAdmissibleCombination_pointDatumY ϑ k _).map (V.ω (1, g)).toLinearMap).bind 1 1 h_term
      (mul_one _).dvd fun _ ↦ by simp
  rw [h_act]
  exact h_moved.smul hc_int fun _ ↦ hc_size

/-- Let `Y j = D.Y j` and `X j = D.X j` be the basis index sets of the spaces `D.spaceY j` and of
the standard definite spaces of rank `D.n j`, for `j ≤ D.m = 2 D.ϱ + 2`, and let `i ≤ D.ϱ`. The
numbers of matrices modulo `D.piM` of the three shapes `Y (2 i + 1) × Y (2 i)`,
`Y (2 i + 2) × Y (2 i + 1)` and `(X (2 i) ⊕ X (2 i + 2)) × X (2 i + 1)` multiply to a divisor of
`D.residueMatrixCount ^ 4`, where `D.residueMatrixCount` is the norm of `D.piM` to the power
`D.n D.m ^ 2`. -/
lemma absNorm_pow_mul_card_dvd_residueMatrixCount_pow {i : ℕ} (hi : i ≤ D.ϱ) :
    absNorm (span {D.piM}) ^ Fintype.card (D.Y (2 * i + 1) × D.Y (2 * i)) *
        absNorm (span {D.piM}) ^ Fintype.card (D.Y (2 * i + 2) × D.Y (2 * i + 1)) *
        Nat.card (PairIndex (D.InitIndex (2 * i)) (D.InitIndex (2 * i + 2)) × D.X (2 * i + 1) →
          Ô D.E ⧸ span {algebraMap (𝓞 D.E) (Ô D.E) D.piM}) ∣
      D.residueMatrixCount ^ 4 := by
  -- All three are powers of the norm of `D.piM`, and all ranks are at most `D.n D.m`.
  have h_m : D.m = 2 * D.ϱ + 2 := D.m_eq_two_mul_varrho_add_two
  let r : ℕ := D.n D.m
  have hY (j : ℕ) (hj : j ≤ 2 * i + 2) : Fintype.card (D.Y j) ≤ r := D.card_Y_le (by lia)
  have hX (j : ℕ) (hj : j ≤ 2 * i + 2) : Fintype.card (D.X j) ≤ r :=
    (D.card_X _).trans_le (D.n_mono (by lia))
  have h_exp :
      Fintype.card (D.Y (2 * i + 1)) * Fintype.card (D.Y (2 * i)) +
          Fintype.card (D.Y (2 * i + 2)) * Fintype.card (D.Y (2 * i + 1)) +
          (Fintype.card (D.X (2 * i)) + Fintype.card (D.X (2 * i + 2))) *
            Fintype.card (D.X (2 * i + 1)) ≤ r ^ 2 * 4 :=
    calc
      _ ≤ r * r + r * r + (r + r) * r := by
        gcongr <;> first | exact hY _ (by lia) | exact hX _ (by lia)
      _ = r ^ 2 * 4 := by ring
  have h_bound : D.residueMatrixCount ^ 4 = absNorm (span {D.piM}) ^ (r ^ 2 * 4) := by
    rw [absNorm_piM, ← pow_mul, ← pow_mul, mul_assoc]
  rw [Nat.card_fun, card_Ô_quot_span D.piM_ne_zero, Nat.card_eq_fintype_card, ← pow_add,
    ← pow_add, h_bound]
  exact pow_dvd_pow _ <| by
    simpa only [Fintype.card_prod, Fintype.card_sum (α := D.X (2 * i))] using h_exp

/-- Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part supported on the finite set of places
`ϑ.Q`, and let `q = ϑ.normQ` be the product of the norms of these places. Let every point `y k` of
the unitary group of `Y k = D.spaceY k` be integral away from `q`. The product `arrowProduct` of the
data `translatedPointDatumY ϑ y k` on `Hom(Y k, Y (k + 1))` and `translatedPointDatumY ϑ y (k + 1)`
on `Hom(Y (k + 1), Y (k + 2))` lies on `Hom(Y (k + 1), (Y k)⁻ ⊕ Y (k + 2))`. It is a finite
combination of translates of the vacuum by matrices that become integral away from `q` after
multiplication by `D.piM` on the rows of `Y k` and by its conjugate on those of `Y (k + 2)`. The
coefficients become integral away from `q` after multiplication by the numbers of matrices modulo
`D.piM` of the two shapes, and if `ϑ.Q` is empty the absolute sum of their images under any
automorphism of `ℂ` is at most `1`. -/
lemma isAdmissibleCombination_arrowProduct_translatedPointDatumY (ϑ : D.TameChar)
    {y : ∀ k : ℕ, Gf D.E (D.Y k)}
    (hy : ∀ k : ℕ, y k ∈ localLevel (D.Y k) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) (k : ℕ) :
    IsAdmissibleCombination
      (fun z : (D.Y k ⊕ D.Y (k + 2)) × D.Y (k + 1) → 𝔸f D.E ↦
        ((D.spaceY (k + 1)).hom (flipSum (D.spaceY k) (D.spaceY (k + 2)))).finHeisenbergOp z
          (vacElem ((D.spaceY (k + 1)).hom (flipSum (D.spaceY k) (D.spaceY (k + 2))))))
      (weightedTranslations ϑ.normQ fun r : (D.Y k ⊕ D.Y (k + 2)) × D.Y (k + 1) ↦
        selfOrConj (algebraMap (𝓞 D.E) (Ô D.E) D.piM) r.1)
      ϑ.normQ
      (absNorm (span {D.piM}) ^ Fintype.card (D.Y (k + 1) × D.Y k) *
        absNorm (span {D.piM}) ^ Fintype.card (D.Y (k + 2) × D.Y (k + 1)))
      (ϑ.Q = ∅) 1
      (arrowProduct (translatedPointDatumY ϑ y k : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1))))
        (translatedPointDatumY ϑ y (k + 1) : 𝒮 ((D.spaceY (k + 1)).hom (D.spaceY (k + 2))))) := by
  -- The product is bilinear and takes two translated vacua to a root of unity times a third.
  have h_bilinear := (D.isAdmissibleCombination_translatedPointDatumY ϑ hy k).map_bilinear
    arrowProduct.toLinearMap₁₂ (D.isAdmissibleCombination_translatedPointDatumY ϑ hy (k + 1))
  rw [abs_one, mul_one] at h_bilinear
  exact h_bilinear.of_eq_isOfFinOrder_smul fun _ ⟨hx, hx'⟩ ↦
    exists_arrowProduct_eq_smul_finHeisenbergOp (β := algebraMap _ (Ô D.E) D.piM) _ _ _ hx hx'

/-- Let `i ≤ D.ϱ`, where the chain of spaces `Y j = D.spaceY j` ends at `j = 2 D.ϱ + 2`. There is a
constant `C` with the following property. Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part
supported on the finite set of places `ϑ.Q`, let `q = ϑ.normQ` be the product of their norms, and
let the points `y k` of the unitary groups of the `Y k` be integral away from `q`. Then
`evaluatedDatum ϑ y i`, the image under `D.doubleLiftEvalY i` of the product of the moved data on
`Hom(Y (2 i), Y (2 i + 1))` and `Hom(Y (2 i + 1), Y (2 i + 2))`, is a finite combination of the
vectors `C • gluedTranslate D.N D.piNPlaces (t₁, t₂)`. The matrices `t₁`, `t₂` are indexed by the
bases `D.X j` of the standard definite spaces and have denominator `star D.piM` away from `q`.
Here `gluedTranslate` is the sum over simple poles at the places `D.piNPlaces` above the prime `D.N`
(`doubleLiftGluing`) applied to the tensor of the two vacua translated by `t₁` and `t₂`. The
coefficients times `D.residueMatrixCount ^ 4`, a power of the norm of `D.piM`, are integral away
from `q`, and if `ϑ.Q` is empty the absolute sum of their images under any automorphism of `ℂ` is at
most `1`. -/
lemma exists_isAdmissibleCombination_evaluatedDatum {i : ℕ} (hi : i ≤ D.ϱ) :
    ∃ C : ℂ, ∀ (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
      (∀ k : ℕ, y k ∈ localLevel (D.Y k) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) →
        IsAdmissibleCombination
          (fun t : (D.X (2 * i + 1) × D.X (2 * i) → 𝔸f D.E) ×
              (D.X (2 * i + 2) × D.X (2 * i + 1) → 𝔸f D.E) ↦
            C • gluedTranslate D.N D.piNPlaces t)
          (translations (D.X (2 * i + 1) × D.X (2 * i)) ϑ.normQ (star (D.piM : 𝔸f D.E)) ×ˢ
            translations (D.X (2 * i + 2) × D.X (2 * i + 1)) ϑ.normQ (star (D.piM : 𝔸f D.E)))
          ϑ.normQ (D.residueMatrixCount ^ 4) (ϑ.Q = ∅) 1 (evaluatedDatum ϑ y i) := by
  -- The product of the two data is a combination of translates `V.finHeisenbergOp z V.vacElem` of
  -- the vacuum of `V = Hom(Y (2 i + 1), (Y (2 i))⁻ ⊕ Y (2 i + 2))`, and the evaluation takes each
  -- of these to a combination of the vectors `C • gluedTranslate …`. Substitute the latter.
  let β : Ô D.E := algebraMap (𝓞 D.E) (Ô D.E) D.piM
  let V := (D.spaceY (2 * i + 1)).hom (flipSum (D.spaceY (2 * i)) (D.spaceY (2 * i + 2)))
  obtain ⟨C, h_eval⟩ : IsAdmissibleEval D.N D.piNPlaces β (D.doubleLiftEvalY i) (selfOrConj β) :=
    D.isAdmissibleEval_doubleLiftEvalY i hi
  refine ⟨C, fun ϑ y hy ↦ ?_⟩
  have h_coprime : D.N.Coprime ϑ.normQ := ϑ.coprime.coprime_mul_left
  have h_product :
      IsAdmissibleCombination (fun z ↦ D.doubleLiftEvalY i (V.finHeisenbergOp z V.vacElem))
        (weightedTranslations ϑ.normQ
          fun r : (D.Y (2 * i) ⊕ D.Y (2 * i + 2)) × D.Y (2 * i + 1) ↦ selfOrConj β r.1) ϑ.normQ
        (absNorm (span {D.piM}) ^ Fintype.card (D.Y (2 * i + 1) × D.Y (2 * i)) *
          absNorm (span {D.piM}) ^ Fintype.card (D.Y (2 * i + 2) × D.Y (2 * i + 1)))
        (ϑ.Q = ∅) 1 (evaluatedDatum ϑ y i) :=
    (D.isAdmissibleCombination_arrowProduct_translatedPointDatumY ϑ hy (2 * i)).map
      (D.doubleLiftEvalY i)
  exact h_product.bind _ 1 (h_eval ϑ.normQ (ϑ.Q = ∅) h_coprime)
    (D.absNorm_pow_mul_card_dvd_residueMatrixCount_pow hi)
    fun _ ↦ by simp

/-- The chain of spaces `Y j = D.spaceY j` ends at `j = D.m = 2 D.ϱ + 2`. There is a constant `C`
with the following property. Let `ϑ` be a tame character of `U(1)(𝔸)`, with tame part supported on
the finite set of places `ϑ.Q`, let `q = ϑ.normQ` be the product of their norms, and let the points
`y k` of the unitary groups of the `Y k` be integral away from `q`. Then the pure tensor of the
vectors `evaluatedDatum ϑ y i` for `i ≤ D.ϱ` is a finite combination of the vectors
`C • D.gluedVacuum t`, where `t` is a tuple of matrices with denominator `star D.piM` away from `q`.
The coefficients times `D.residueMatrixCount ^ (2 * D.m)`, a power of the norm of `D.piM`, are
integral away from `q`, and if `ϑ.Q` is empty the absolute sum of their images under any
automorphism of `ℂ` is at most `1`. -/
lemma exists_isAdmissibleCombination_gluedVacuum :
    ∃ C : ℂ, ∀ (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
      (∀ k : ℕ, y k ∈ localLevel (D.Y k) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) →
        IsAdmissibleCombination (fun t : D.Translations ↦ C • D.gluedVacuum t)
          (admissibleTranslations ϑ.normQ)
          ϑ.normQ (D.residueMatrixCount ^ (2 * D.m)) (ϑ.Q = ∅) 1
          (pure (evaluatedDatum ϑ y) (D.ϱ + 1)) := by
  -- Tensor the combinations of the pairs, and divide each constant by the factors `κ` that relate
  -- the integral vacuum to the vacuum.
  let glued (i : ℕ) (t : D.Translations) :
      (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart :=
    gluedTranslate D.N D.piNPlaces (t (2 * i), t (2 * i + 1))
  choose! C hC using fun (i : ℕ) (hi : i ≤ D.ϱ) ↦ D.exists_isAdmissibleCombination_evaluatedDatum hi
  -- `translateDatum t j` translates the integral vacuum, which is `κ j` times the vacuum.
  let κ (j : ℕ) : ℂ := P.vacuumScale D.towerExp ^ Fintype.card (D.X (j + 1) × D.X j)
  have h_datum (t : D.Translations) (j : ℕ) : D.translateDatum t j =
      κ j • (D.homX j).heisenbergFinPart (t j) ⟨vacElem _, vacElem_mem_finitePart⟩ :=
    ((D.homX j).heisenbergFinPart (t j)).map_smul (κ j) ⟨vacElem _, vacElem_mem_finitePart⟩
  let c (i : ℕ) : ℂ := C i / (κ (2 * i) * κ (2 * i + 1))
  have h_factor (t : D.Translations) (i : ℕ) :
      C i • glued i t = c i • D.gluedDoubleLiftDatum (D.translateDatum t) i := by
    have h_const : c i * (κ (2 * i) * κ (2 * i + 1)) = C i := div_mul_cancel₀ _ (by simp [κ])
    simp only [glued, gluedTranslate, gluedDoubleLiftDatum, h_datum, smul_tmul_smul, map_smul,
      smul_smul, h_const]
  have h_pure (t : D.Translations) : pure (fun i ↦ C i • glued i t) (D.ϱ + 1) =
      (∏ i ∈ range (D.ϱ + 1), c i) • D.gluedVacuum t :=
    pure_smul _ c _ fun i _ ↦ h_factor t i
  have h_den : (D.residueMatrixCount ^ 4) ^ (D.ϱ + 1) = D.residueMatrixCount ^ (2 * D.m) := by
    rw [← pow_mul, D.m_eq_two_mul_varrho_add_two]
    ring
  refine ⟨∏ i ∈ range (D.ϱ + 1), c i, fun ϑ y hy ↦ ?_⟩
  have h_tensor :
      IsAdmissibleCombination (fun t : D.Translations ↦ pure (fun i ↦ C i • glued i t) (D.ϱ + 1))
        (admissibleTranslations ϑ.normQ) ϑ.normQ ((D.residueMatrixCount ^ 4) ^ (D.ϱ + 1)) (ϑ.Q = ∅)
        (|1| ^ (D.ϱ + 1)) (pure (evaluatedDatum ϑ y) (D.ϱ + 1)) :=
    .pure (v := fun i x ↦ C i • gluedTranslate D.N D.piNPlaces x)
      (A := fun j ↦ translations (D.X (j + 1) × D.X j) ϑ.normQ (star (D.piM : 𝔸f D.E)))
      (D.residueMatrixCount ^ 4) 1 (D.ϱ + 1) fun i hi ↦ hC i (Nat.le_of_lt_succ hi) ϑ y hy
  simpa only [h_pure, h_den, abs_one, one_pow] using h_tensor

end New.Data
