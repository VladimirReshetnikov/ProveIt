import Lib.Weil.DualPair.ThetaLiftConvergence
import Lib.Weil.Periods.ConstantTerm

/-!
# One step of the seesaw unfolding of the theta integral over the Bessel group

This file unfolds the period of an equivariant function `W` (`New.Grading.IsEquivariant`) on the
Bessel group `New.Grading.besselGroup` of `Y` against the theta kernel, where the strings of `Y`
and `Y'` have lengths `s` and `s - 1`. The theta kernel at `(r, h)` is `θ` of the translate
`twistedPairWeil α (r, h) Φ`; it is expanded in constant terms indexed by rational maps `V → V'`
modulo those of degree at least zero (`New.Grading.nonnegMaps`). Over a set of classes that is
stable under the rational points of the Bessel group and in which no chosen representative survives
(`New.Grading.Survives`), the sum of the terms integrates to zero. Hence only the translates of
`𝒞 = New.Grading.agreeingClasses` by the rational points of `U(V')` contribute. This writes the
period as a sum of values of `New.Grading.unfoldStep`, and its integral against a rapidly decreasing
automorphic `y` as an integral of `New.Grading.unfoldStep` times `y`.

## Main definitions and results

* `New.Grading.hasSum_unfoldStep`: for `W` equivariant, the period of `W` against the theta kernel
  at `h` is the sum of the values of `New.Grading.unfoldStep` at `γ h` over the rational points `γ`
  of `U(V')`, modulo those of `Y'.besselGroup` on the left.
* `New.Grading.integral_besselGroup_unfold`: the period of `W` against the theta integral of a
  rapidly decreasing automorphic `y` unfolds to the integral of `New.Grading.unfoldStep` times `y`
  modulo the rational points of `Y'.besselGroup`.

Notions from other files:
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Grading.ratBessel`: The rational points of U(V) that lie in the Bessel (Fourier–Jacobi)
  subgroup of the grading Y.
* `New.Grading.constTerm`: the constant term of `f` at `w` along the maps of positive degree.
* `New.Grading.unfoldStep`: the function `h ↦ ∫ W(r) * Y.constTermAtStringMap Y' α f r h dr` on
  U(V′)(𝔸), integrated over the Bessel group of `Y` modulo its rational points.
* `New.Grading.agreeingClasses`: the set `𝒞` of classes whose chosen representative agrees with
  `T = Y.stringMap Y'` (`New.Grading.AgreesWithStringMap`).

## Relation to the literature

Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding step).
Here the setting is unitary pairs and hook orbits with a definite complement, and the Bessel and
Fourier–Jacobi cases are treated together. The period is taken against any continuous automorphic
function with the generic unipotent character, for a rapidly decreasing form, and the unfolded
integral converges absolutely. Source: B. Wang Peng Jun, Global theta lifting and automorphic
periods associated to nilpotent orbits, J. Number Theory 271 (2025) 122–149, Prop. 3.2 and Thm. 4.5;
for the local case, R. Gomez, C.-B. Zhu, GAFA 24 (2014) 796–853; for unitary hooks, M. Furusawa, K.
Morimoto, Math. Ann. 391 (2025) §3.
-/

noncomputable section

/-- Suppose that for every `y` in `C`, the point `γ • y` lies in `C` exactly when `γ` lies in `S`,
and let `D` be the union of the translates of `C`. Then `(q, y) ↦ q.out • y` is a bijection from the
pairs of a left coset of `S` and a point of `C` onto `D`. -/
lemma New.exists_equiv_quotient_prod_block {Λ Y : Type*} [Group Λ] [MulAction Λ Y] {S : Subgroup Λ}
    {C D : Set Y} (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) :
    ∃ e : (Λ ⧸ S) × C ≃ D, ∀ (q : Λ ⧸ S) (y : C), (e (q, y) : Y) = q.out • (y : Y) := by
  let f (p : (Λ ⧸ S) × C) : D := ⟨p.1.out • (p.2 : Y), (hD _).2 ⟨p.1.out⁻¹, by simp⟩⟩
  have f_inj : Function.Injective f := by
    rintro ⟨q, y⟩ ⟨q', y'⟩ h_eq
    have h_smul : q.out • (y : Y) = q'.out • (y' : Y) := congrArg Subtype.val h_eq
    have h_mem : q.out⁻¹ * q'.out ∈ S :=
      (hC _ _ y'.2).1 (by simp [mul_smul, ← h_smul])
    obtain rfl : q = q' := by simpa using QuotientGroup.eq.2 h_mem
    exact Prod.ext rfl (Subtype.ext (MulAction.injective _ h_smul))
  have f_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, hγ⟩ := (hD y).1 hy
    let q : Λ ⧸ S := (γ⁻¹ : Λ)
    have h_mem : q.out⁻¹ * γ⁻¹ ∈ S := QuotientGroup.eq.1 q.out_eq'
    have h_block : q.out⁻¹ • y ∈ C := by simpa [mul_smul] using (hC _ _ hγ).2 h_mem
    exact ⟨(q, ⟨q.out⁻¹ • y, h_block⟩), Subtype.ext (smul_inv_smul q.out y)⟩
  exact ⟨.ofBijective f ⟨f_inj, f_surj⟩, fun _ _ ↦ rfl⟩

namespace New.Grading

open Subgroup MeasureTheory Set MulAction ProbabilityTheory Space QuotientAddGroup Subtype ENNReal
  ContinuousLinearMap

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {s : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N X s} (Y' : Grading V' N X' (s - 1)) [WeilData E]
  (α : ∀ (n : Type) [Fintype n], AutChar E) (Φ : 𝒮 (V.hom V')) {W : Y.besselGroup → ℂ} {d : ι' → ℤ}

/-- For a pair `p = (γ, δ)` of rational points, the substitution `w ↦ δ w γ⁻¹` on rational maps
`V → V'`, with `γ` and `δ` in rational coordinates. -/
noncomputable def ratSubst (p : Y.ratBessel × V'.ratParabolic d) :
    ratMatrices E ι' ι →+ ratMatrices E ι' ι :=
  .mk' (fun w ↦ ⟨V'.ratCoordMatrix p.2 * (w.1 * V.ratCoordMatrix p⁻¹.1),
    mul_mem_ratMatrices p⁻¹.1.2.1 p.2.2.1 w.2⟩) (by simp [Matrix.add_mul, Matrix.mul_add])

section

omit [WeilData E]

/-- The substitution `w ↦ δ w γ⁻¹` keeps the maps of degree `≥ 0`. -/
lemma nonnegMaps_le_comap_ratSubst (p : Y.ratBessel × V'.ratParabolic d) :
    Y.nonnegMaps d ≤ (Y.nonnegMaps d).comap (ratSubst p) := fun w hw ↦ by
  obtain ⟨-, δ_tri⟩ := p.2.property
  obtain ⟨-, γ_bessel⟩ := p⁻¹.1.property
  have h_left : HasDegreeGe d d 0 (V'.ratCoordMatrix p.2) := fun _ _ _ ↦ δ_tri (by lia)
  have h_right : HasDegreeGe Y.gradeOf Y.gradeOf 0 (V.ratCoordMatrix p⁻¹.1) :=
    Y.hasDegreeGe_zero_of_mem_besselGroup γ_bessel
  exact h_left.mul (HasDegreeGe.mul hw h_right le_rfl) le_rfl

/-- A pair `(γ, δ)` acts on the classes of rational maps by `w ↦ δ w γ⁻¹`. -/
noncomputable instance :
    MulAction (Y.ratBessel × V'.ratParabolic d) (ratMatrices E ι' ι ⧸ Y.nonnegMaps d) where
  smul p := map _ _ (ratSubst p) (nonnegMaps_le_comap_ratSubst p)
  one_smul := by simp [forall_mk, HSMul.hSMul, ratSubst]
  mul_smul := by simp [forall_mk, HSMul.hSMul, ratSubst, Matrix.mul_assoc]

/-- The chosen representative of `(γ, δ) • w` lies in the class of `δ w γ⁻¹`, formed with the
chosen representative of `w`. -/
lemma mk_out_smul (p : Y.ratBessel × V'.ratParabolic d) (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :
    ((p • w).out : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) = ratSubst p w.out :=
  (p • w).out_eq'.trans (congrArg _ w.out_eq'.symm)

omit [Fintype X'] in
/-- If `d ≤ Y'.gradeOf ⊔ 0`, the class `(γ, δ) • w` agrees with `T = Y.stringMap Y'` exactly if
`δ w γ⁻¹` does. -/
lemma agreesWithStringMap_out_smul (hd_le : d ≤ Y'.gradeOf ⊔ 0)
    (p : Y.ratBessel × V'.ratParabolic d) (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :
    Y.AgreesWithStringMap Y' (p • w).out ↔
      Y.AgreesWithStringMap Y' (V'.ratCoordMatrix p.2 * (w.out.1 * V.ratCoordMatrix p⁻¹.1)) :=
  agreesWithStringMap_congr_rat hd_le (mk_out_smul p w)

end

variable (W) in
/-- The term of the class `w`: the value `W r` times the constant term, at the chosen
representative of `w`, of the twisted Weil translate of `Φ` by `(r, h)`. For weights `d` odd under
`Y'.stringReversal` any representative gives the same value (`constTerm_out`). -/
noncomputable def classTerm (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) (h : G E ε')
    (r : Y.besselGroup) : ℂ :=
  W r * Y.constTerm d (twistedPairWeil α (r.1, h) Φ) w.out

/-- For `W` equivariant and `d` odd, the term of a class is jointly continuous in `(h, r)`. -/
lemma continuous_classTerm (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :
    Continuous ↿(classTerm α Φ W w) := by
  -- The constant term is a continuous linear form of the datum.
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  have W_cont : Continuous W := hW.continuous
  unfold classTerm
  simp only [constTerm_eq_theta_zeroTerm D h_frame]
  fun_prop

/-- For `W` equivariant and `d` odd, rational pairs permute the terms: the term of `(γ, δ) • w` at
`(δ h, γ r)` is the term of `w` at `(h, r)`. -/
lemma classTerm_smul (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (γ : Y.ratBessel) (δ : V'.ratParabolic d)
    (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) (h : G E ε') (r : Y.besselGroup) :
    classTerm α Φ W ((γ, δ) • w) (δ * h) (Subgroup.inclusion inf_le_right γ * r) =
      classTerm α Φ W w h r := by
  -- The constant term may be read at `δ w γ⁻¹`, and translating by `(γ, δ)` substitutes back.
  rw [classTerm, hW.rat_mul _ γ.2.1 r, constTerm_congr_rat hd _ _ (mk_out_smul (γ, δ) w)]
  simp [classTerm, ratSubst, constTerm_mul_of_mem_ratBessel hd γ.2 δ.2, Matrix.mul_assoc,
    ← map_mul, ← (V'.ratCoordMatrix _⁻¹).mul_assoc]

/-- Let `W` on the Bessel group of `Y` be equivariant (`New.Grading.IsEquivariant`) and let the
weights `d` be odd under `Y'.stringReversal`. The sum of the norms of the terms
`classTerm α Φ W w h r` over any set `S` of classes of rational maps is at most a constant times the
operator norm of the Weil action of `(1, δ h)`, for every `δ` in `V'.ratParabolic d` (the rational
points that do not lower `d`), uniformly in `r`. -/
lemma exists_tsum_enorm_classTerm_le (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    ∃ a : NNReal, ∀ (h : G E ε') (δ : V'.ratParabolic d)
      (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)) (r : Y.besselGroup),
      ∑' w : S, ‖classTerm α Φ W w.1 h r‖ₑ ≤ ‖pairWeil V V' (α ι) (α ι') (1, δ * h)‖ₑ * a := by
  -- The norms of the constant terms of any datum `Ψ` have sum at most `b ‖Ψ‖`. Every `r` has a
  -- rational translate `γ * r` in the compact set `K`, and for `r` in `K` the datum
  -- `W r • twistedPairWeil α (r, 1) Φ` has norm at most `a`.
  have W_cont : Continuous W := hW.continuous
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  obtain ⟨b, hb⟩ : ∃ b : NNReal, ∀ Ψ : 𝒮 (V.hom V'),
      ∑' w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d, ‖Y.constTerm d Ψ w.out‖ₑ ≤ b * ‖Ψ‖ₑ :=
    Y.exists_tsum_enorm_constTerm_le hd
  obtain ⟨K, hK, K_covers⟩ := Y.isCocompact_ratBessel
  obtain ⟨a, ha⟩ : BddAbove
      ((fun r : Y.besselGroup ↦ ‖W r • twistedPairWeil α (r.1, 1) Φ‖₊) '' K) :=
    hK.bddAbove_image (by with_reducible fun_prop)
  refine ⟨b * a, fun h δ S r ↦ ?_⟩
  obtain ⟨γ, γ_rat, γ_mem⟩ := K_covers r
  let γ₀ : Y.ratBessel := ⟨γ, γ_rat⟩
  set ρ : 𝒮 (V.hom V') →L[ℂ] 𝒮 (V.hom V') := pairWeil V V' (α ι) (α ι') (1, δ * h) with hρ
  set Ψ : 𝒮 (V.hom V') := W (γ * r) • twistedPairWeil α ((γ * r).1, 1) Φ with hΨ
  have Ψ_le : ‖Ψ‖ₑ ≤ a := ENNReal.coe_le_coe.2 (ha ⟨γ * r, γ_mem, rfl⟩)
  -- The constant term is linear in the datum, and `(1, δ h) (γ r, 1) = (γ r, δ h)`.
  have term_eq (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :
      classTerm α Φ W w (δ * h) (γ * r) = Y.constTerm d (ρ Ψ) w.out := by
    simp [hρ, hΨ, classTerm, constTerm_eq_theta_zeroTerm D h_frame, rep_apply_apply]
  calc _ = ∑' w : S, ‖classTerm α Φ W ((γ₀, δ) • w.1) (δ * h) (γ * r)‖ₑ :=
        tsum_congr fun w ↦ congrArg _ (classTerm_smul Y' α Φ hW hd γ₀ δ w h r).symm
    _ ≤ ∑' w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d, ‖classTerm α Φ W w (δ * h) (γ * r)‖ₑ :=
        tsum_comp_le_tsum_of_injective (MulAction.injective (γ₀, δ)).injOn.injective
          fun w ↦ ‖classTerm α Φ W w (δ * h) (γ * r)‖ₑ
    _ ≤ b * ‖ρ Ψ‖ₑ := by simpa only [term_eq] using hb (ρ Ψ)
    _ ≤ b * (‖ρ‖ₑ * a) := by grw [ρ.le_opENorm, Ψ_le]
    _ = ‖ρ‖ₑ * (b * a : NNReal) := by rw [ENNReal.coe_mul, mul_left_comm]

/-- For `W` equivariant and `d` odd, the sum of the norms of the terms has finite integral for
`Y.besselMeasure`. -/
lemma lintegral_tsum_enorm_classTerm_lt_top (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (h : G E ε')
    (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)) :
    ∫⁻ r : Y.besselGroup, ∑' w : S, ‖classTerm α Φ W w.1 h r‖ₑ ∂Y.besselMeasure < ∞ := by
  obtain ⟨a, ha⟩ := exists_tsum_enorm_classTerm_le Y' α Φ hW hd
  exact IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal Y.besselMeasure ⟨_, ha h 1 S⟩

/-- For `W` equivariant and `d` odd, the terms can be integrated one by one: their integrals add up
to the integral of the sum. -/
lemma hasSum_integral_classTerm (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (h : G E ε')
    (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)) :
    HasSum (fun w : S ↦ ∫ r : Y.besselGroup, classTerm α Φ W w.1 h r ∂Y.besselMeasure)
      (∫ r : Y.besselGroup, ∑' w : S, classTerm α Φ W w.1 h r ∂Y.besselMeasure) := by
  have term_cont (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) : Continuous ↿(classTerm α Φ W w) :=
    continuous_classTerm Y' α Φ hW hd w
  exact hasSum_integral_of_lintegral_tsum_lt_top
    (lintegral_tsum_enorm_classTerm_lt_top Y' α Φ hW hd h S)

/-- Let `W` be equivariant and `d` odd. If the chosen representative of `w` does not survive
(`New.Grading.Survives`), left translation by some `u` multiplies the term of `w` by a constant
`c ≠ 1` of modulus one. -/
lemma exists_classTerm_mul_eq_of_not_survives (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (h : G E ε')
    {w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d} (h_killed : ¬Y.Survives Y' d w.out) :
    ∃ (u : Y.besselGroup) (c : ℂ), ‖c‖ = 1 ∧ c ≠ 1 ∧
      ∀ r : Y.besselGroup, classTerm α Φ W w h (u * r) = c • classTerm α Φ W w h r := by
  obtain ⟨u, hu, ⟨u_deg, wu_deg⟩, phase_ne⟩ : ∃ u ∈ Y.unipotent,
      (HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1) ∧
        HasDegreeGe d Y.gradeOf 1 (w.out.1 * (V.ratCoordMatrix u - 1))) ∧
      V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') ≠
        V.homBicharacter V' (w.out.1 * V.ratCoordMatrix u) w.out := by
    simpa only [not_forall, exists_prop] using h_killed
  -- The constant is the quotient of the two phases (`IsEquivariant.unipotent_mul_constTerm`).
  let u' : Y.besselGroup := ⟨u, Y.unipotent_le_besselGroup hu⟩
  exact ⟨u', _, by simp [Heisenberg.norm_eq_one], div_ne_one_of_ne phase_ne,
    fun r ↦ hW.unipotent_mul_constTerm hd (u := u') u_deg wu_deg r h⟩

/-- Let `W` on `Y.besselGroup` be equivariant (`New.Grading.IsEquivariant`) and let `d` be odd under
`Y'.stringReversal`. Let `S` be a set of classes of rational matrices modulo `Y.nonnegMaps d` that
is stable under `Y.ratBessel` and such that no chosen representative survives
(`New.Grading.Survives`). Then for every `h`, the sum over `S` of the terms `classTerm α Φ W w h`
(`W r` times a constant term of the Weil translate of `Φ`) has integral `0` for
`Y.besselMeasure`. -/
lemma integral_tsum_classTerm_eq_zero (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (h : G E ε')
    {S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)} (h_killed : ∀ w ∈ S, ¬Y.Survives Y' d w.out)
    (h_stable : ∀ w ∈ S, ∀ γ : Y.ratBessel, (γ, (1 : V'.ratParabolic d)) • w ∈ S) :
    ∫ r : Y.besselGroup, ∑' w : S, classTerm α Φ W w.1 h r ∂Y.besselMeasure = 0 := by
  have term_cont (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) : Continuous ↿(classTerm α Φ W w) :=
    continuous_classTerm Y' α Φ hW hd w
  -- `Y.ratBessel` acts on `S`, and embeds by `i` in the Bessel group; the terms are equivariant.
  let := compHom (ratMatrices E ι' ι ⧸ Y.nonnegMaps d) (.inl Y.ratBessel (V'.ratParabolic d))
  let Z : SubMulAction Y.ratBessel (ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :=
    ⟨S, fun γ w hw ↦ h_stable w hw γ⟩
  let i : Y.ratBessel →* Y.besselGroup := Subgroup.inclusion inf_le_right
  have term_smul (γ : Y.ratBessel) (w : Z) (r : Y.besselGroup) :
      classTerm α Φ W (γ • w : Z).1 h (i γ * r) = classTerm α Φ W w.1 h r := by
    change classTerm α Φ W ((γ, (1 : V'.ratParabolic d)) • w.1) h _ = _
    simpa using classTerm_smul Y' α Φ hW hd γ 1 w h r
  -- Each orbit unfolds to an integral over the quotient by the stabiliser; there left translation
  -- by some `u` multiplies the term by a constant `c ≠ 1` of modulus one.
  have orbit_zero (q : Quot (orbitRel Y.ratBessel Z)) : ∑' w : Quot.mk _ ⁻¹' {q},
      ∫ r : Y.besselGroup, classTerm α Φ W (w.1 : Z).1 h r ∂Y.besselMeasure = 0 := by
    obtain ⟨o⟩ := q
    obtain ⟨u, c, c_norm, c_ne, twist⟩ :=
      exists_classTerm_mul_eq_of_not_survives Y' α Φ hW hd h (h_killed _ o.2)
    -- The stabiliser is written as an intersection so that it is seen to be discrete.
    have stab_eq : (stabilizer Y.ratBessel o).map i =
        Y.ratBessel.subgroupOf Y.besselGroup ⊓ (stabilizer Y.ratBessel o).map i :=
      right_eq_inf.2 ((map_le_range ..).trans (inclusion_range _).le)
    have mem_orbit (w : Z) :
        w ∈ Quot.mk (orbitRel Y.ratBessel Z) ⁻¹' {Quot.mk _ o} ↔ o ∈ orbit Y.ratBessel w :=
      Quotient.eq.trans comm
    obtain ⟨fixes, unfold⟩ := integral_tsum_orbit (μ := .haar)
      (k := fun w : Z ↦ classTerm α Φ W w.1 h) (inclusion_injective _) (inclusion_range _)
      (by fun_prop) term_smul stab_eq mem_orbit
    obtain ⟨-, -, sum_eq⟩ := unfold (.inl (lintegral_tsum_enorm_classTerm_lt_top Y' α Φ hW hd h S))
    exact sum_eq.trans
      (integral_quotMeasure_eq_zero_of_twist _ fixes (by fun_prop) c_norm c_ne twist)
  -- Integrate term by term and group the terms by orbits.
  rw [← ((hasSum_integral_classTerm Y' α Φ hW hd h S).tsum_fiberwise
    (Quot.mk (orbitRel Y.ratBessel Z))).tsum_eq]
  exact (tsum_congr orbit_zero).trans tsum_zero

/-- Let `W` be equivariant and `d` odd. Let `A ⊆ B` be sets of classes such that `B \ A` is stable
under `Y.ratBessel` and no chosen representative of a class in `B \ A` survives
(`New.Grading.Survives`). Then `B \ A` may be dropped: the sum over `A` of the integrals of the
terms is the integral of the sum over `B`. -/
lemma tsum_integral_eq_of_not_survives (hW : Y.IsEquivariant W)
    (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (h : G E ε')
    {A B : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)} (hAB : A ⊆ B)
    (h_killed : ∀ w ∈ B \ A, ¬Y.Survives Y' d w.out)
    (h_stable : ∀ w ∈ B \ A, ∀ γ : Y.ratBessel, (γ, (1 : V'.ratParabolic d)) • w ∈ B \ A) :
    ∑' w : A, ∫ r : Y.besselGroup, classTerm α Φ W w.1 h r ∂Y.besselMeasure =
      ∫ r : Y.besselGroup, ∑' w : B, classTerm α Φ W w.1 h r ∂Y.besselMeasure := by
  -- Integrate term by term over `A`, `B \ A` and `B`; the part over `B \ A` is zero.
  let period (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) : ℂ :=
    ∫ r, classTerm α Φ W w h r ∂Y.besselMeasure
  let total (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)) : ℂ :=
    ∫ r, ∑' w : S, classTerm α Φ W w.1 h r ∂Y.besselMeasure
  have termwise (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d)) :
      HasSum (fun w : S ↦ period w) (total S) :=
    hasSum_integral_classTerm Y' α Φ hW hd h S
  have dropped : total (B \ A) = 0 :=
    integral_tsum_classTerm_eq_zero Y' α Φ hW hd h h_killed h_stable
  have split : HasSum (fun w : ↥(A ∪ B \ A) ↦ period w) (total A + total (B \ A)) :=
    HasSum.add_disjoint (f := period) disjoint_sdiff_right (termwise A) (termwise (B \ A))
  rw [union_sdiff_cancel hAB, dropped, add_zero] at split
  exact (termwise A).tsum_eq.trans (split.unique (termwise B))

variable (Y) in
/-- For the weights `d = 0`, the union of the translates of `𝒞` by the rational points of `U(V')`:
the classes that some rational `δ` moves into `𝒞`. -/
def agreeingTranslates : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) :=
  {w : ratMatrices E ι' ι ⧸ Y.nonnegMaps 0 |
    ∃ δ : V'.ratParabolic 0, ((1 : Y.ratBessel), δ) • w ∈ Y.agreeingClasses Y' 0}

omit [WeilData E] in
/-- For `d ≤ Y'.gradeOf ⊔ 0`, a pair `p = (γ, δ)` keeps a class of `𝒞 = Y.agreeingClasses Y' d`
in `𝒞` exactly if `δ` lies in the Bessel group of `Y'`. -/
lemma smul_mem_agreeingClasses_iff (hd_le : d ≤ Y'.gradeOf ⊔ 0)
    (p : Y.ratBessel × V'.ratParabolic d) {w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d}
    (hw : w ∈ Y.agreeingClasses Y' d) :
    p • w ∈ Y.agreeingClasses Y' d ↔ (p.2 : G E ε') ∈ Y'.besselGroup := by
  have h_inv : (p⁻¹.1 : G E ε) ∈ Y.besselGroup := (mem_inf.1 p⁻¹.1.property).right
  exact (agreesWithStringMap_out_smul Y' hd_le p w).trans
    (Y.agreesWithStringMap_mul_iff Y' h_inv hw p.2)

include Y' in
/-- For the weights `d = 0`, the terms of all classes add up to `W r` times the theta kernel. -/
lemma tsum_classTerm (h : G E ε') (r : Y.besselGroup) :
    ∑' w : (univ : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0)), classTerm α Φ W w.1 h r =
      W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) := by
  simp [classTerm, tsum_mul_left,
    (tsum_univ _).trans (Y.hasSum_constTerm_out (Y' := Y') (d := 0) (by simp)).tsum_eq]

/-- Take the weights `d = 0` and `W` equivariant. Only the classes in `Y.agreeingTranslates Y'`, the
rational translates of the classes that agree with `T = Y.stringMap Y'`, contribute: the integrals
of their terms `classTerm α Φ W w h` add up to the period of `W` against the theta kernel. -/
lemma tsum_agreeingTranslates (hW : Y.IsEquivariant W) (h : G E ε') :
    ∑' w : Y.agreeingTranslates Y', ∫ r : Y.besselGroup, classTerm α Φ W w.1 h r ∂Y.besselMeasure =
      ∫ r : Y.besselGroup, W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) ∂Y.besselMeasure := by
  have h_killed : ∀ w ∈ univ \ Y.agreeingTranslates Y', ¬Y.Survives Y' 0 w.out := by
    -- If `w` survives, some rational `δ` makes `δ w` agree with `T`.
    rintro w ⟨-, hw⟩ survives
    obtain ⟨δ, δ_rat, agrees⟩ : ∃ δ ∈ V'.Γ,
        Y.AgreesWithStringMap Y' (V'.ratCoordMatrix δ * (w.out : Matrix ι' ι (𝔸 E))) :=
      Y.exists_agreesWithStringMap Y' w.out w.out.property survives
    let δ₀ : V'.ratParabolic 0 := ⟨δ, δ_rat, nofun⟩
    have δ₀_smul : ((1 : Y.ratBessel), δ₀) • w ∈ Y.agreeingClasses Y' 0 :=
      (agreesWithStringMap_out_smul Y' (by simp) (1, δ₀) w).2 (by simpa using agrees)
    exact hw ⟨δ₀, δ₀_smul⟩
  have h_stable : ∀ w ∈ univ \ Y.agreeingTranslates Y', ∀ γ : Y.ratBessel,
      (γ, (1 : V'.ratParabolic 0)) • w ∈ univ \ Y.agreeingTranslates Y' := by
    -- If `(γ, δ) • w` agrees with `T`, so does `(1, δ) • w`: apply `(γ⁻¹, 1)`.
    rintro w ⟨-, hw⟩ γ
    refine ⟨mem_univ _, fun ⟨δ, hδ⟩ ↦ hw ⟨δ, ?_⟩⟩
    simpa [smul_smul] using smul_mem_agreeingClasses_iff Y' (by simp) (γ⁻¹, 1) hδ
  simp only [← tsum_classTerm Y' α Φ]
  exact tsum_integral_eq_of_not_survives Y' α Φ hW (by simp) h (subset_univ _) h_killed h_stable

/-- For `W` equivariant, the integrals of the terms of `𝒞` add up to `Y.unfoldStep Y' α Φ W h`:
expanded again for the weights `Y'.gradeOf`, only the class of `T` survives. -/
lemma tsum_integral_classTerm_agreeingClasses (hW : Y.IsEquivariant W) (h : G E ε') :
    ∑' w : Y.agreeingClasses Y' 0, ∫ r : Y.besselGroup, classTerm α Φ W w.1 h r ∂Y.besselMeasure =
      Y.unfoldStep Y' α Φ W h := by
  let T : ratMatrices E ι' ι := ⟨Y.stringMap Y', _, rfl⟩
  have T_mem : ↑T ∈ Y.agreeingClasses Y' Y'.gradeOf :=
    (agreesWithStringMap_congr_rat le_sup_left (out_eq' _)).2 fun _ _ _ _ ↦ rfl
  have T_fixed (γ : Y.ratBessel) :
      (γ, (1 : V'.ratParabolic Y'.gradeOf)) •
        (T : ratMatrices E ι' ι ⧸ Y.nonnegMaps Y'.gradeOf) = T :=
    eq_iff_sub_mem.2 (Y.hasDegreeGe_zero_mul_stringMap_mul_sub γ⁻¹.2.2 (one_mem _))
  calc _ = ∫ r, ∑' w : Y.agreeingClasses Y' 0, classTerm α Φ W w.1 h r ∂Y.besselMeasure :=
        (hasSum_integral_classTerm Y' α Φ hW (by simp) h _).tsum_eq
    _ = ∫ r, ∑' w : Y.agreeingClasses Y' Y'.gradeOf, classTerm α Φ W w.1 h r ∂Y.besselMeasure := by
        -- Both sums give the same Fourier coefficient, which does not depend on the weights.
        simp (disch := simp) only [classTerm, tsum_mul_left, Y.tsum_constTerm_agreesWithStringMap]
    _ = ∑' w : ({↑T} : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps Y'.gradeOf)),
          ∫ r, classTerm α Φ W w.1 h r ∂Y.besselMeasure := by
        refine (tsum_integral_eq_of_not_survives Y' α Φ hW Y'.gradeOf_stringReversal h
          (singleton_subset_iff.2 T_mem)
          (fun w ⟨agrees, ne_T⟩ survives ↦ ne_T ?_) fun w ⟨agrees, ne_T⟩ γ ↦ ?_).symm
        · -- A class of `𝒞` that survives is the class of `T`.
          exact w.out_eq'.symm.trans
            (eq_iff_sub_mem.2 (Y.hasDegreeGe_of_survives _ agrees survives))
        · -- `Y.ratBessel` keeps `𝒞` and fixes the class of `T`, so it moves no other class to it.
          exact ⟨(smul_mem_agreeingClasses_iff Y' le_sup_left _ agrees).2 (one_mem _),
            ((MulAction.injective _).ne ne_T).trans_eq (T_fixed γ)⟩
    _ = Y.unfoldStep Y' α Φ W h := by
        simp only [(hasSum_unique _).tsum_eq, default_coe_singleton, classTerm,
          constTerm_out Y'.gradeOf_stringReversal, unfoldStep, T]

/-- Let `W` be equivariant and `𝒞 = Y.agreeingClasses Y' 0`. The union of the translates of `𝒞` is
in bijection with the pairs of a left coset `q` of `Y'.ratBessel` in `V'.Γ` and a class `w` of `𝒞`,
such that the term of `(q, w)` at `h` is the term of `w` at `γ⁻¹ h`, where `γ` is the chosen
representative of `q`. -/
lemma exists_equiv_agreeingTranslates (hW : Y.IsEquivariant W) :
    ∃ e : (V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) × Y.agreeingClasses Y' 0 ≃ Y.agreeingTranslates Y',
      ∀ (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) (w : Y.agreeingClasses Y' 0) (h : G E ε'),
        classTerm α Φ W (e (q, w)).1 h = classTerm α Φ W w.1 ((q.out : G E ε')⁻¹ * h) := by
  -- For `d = 0` the parabolic condition is empty, so `V'.Γ` acts on classes through `δ ↦ (1, δ)`.
  -- It keeps a class of `𝒞` in `𝒞` exactly on `Y'.ratBessel`, so the translates are blocks.
  have rat_le : V'.Γ ≤ V'.ratParabolic 0 := fun δ δ_rat ↦ ⟨δ_rat, nofun⟩
  let i : V'.Γ →* V'.ratParabolic 0 := Subgroup.inclusion rat_le
  let : MulAction V'.Γ (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) :=
    compHom _ ((MonoidHom.inr Y.ratBessel (V'.ratParabolic 0)).comp i)
  have smul_eq (δ : V'.Γ) (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) :
      δ • w = ((1 : Y.ratBessel), i δ) • w := rfl
  have keeps_iff (δ : V'.Γ) (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps 0)
      (hw : w ∈ Y.agreeingClasses Y' 0) :
      δ • w ∈ Y.agreeingClasses Y' 0 ↔ δ ∈ Y'.ratBessel.subgroupOf V'.Γ :=
    (smul_mem_agreeingClasses_iff Y' (by simp) (1, i δ) hw).trans (and_iff_right δ.property).symm
  have translates_iff (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) :
      w ∈ Y.agreeingTranslates Y' ↔ ∃ δ : V'.Γ, δ • w ∈ Y.agreeingClasses Y' 0 := by
    constructor
    · rintro ⟨⟨δ, δ_rat, δ_parab⟩, hδ⟩
      exact ⟨⟨δ, δ_rat⟩, hδ⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨i δ, hδ⟩
  obtain ⟨e, he⟩ := exists_equiv_quotient_prod_block keeps_iff translates_iff
  refine ⟨e, fun q w h ↦ funext fun r ↦ ?_⟩
  rw [he, smul_eq]
  simpa [i] using classTerm_smul Y' α Φ hW (by simp) 1 (i q.out) w ((q.out : G E ε')⁻¹ * h) r

/-- For `W` equivariant and every `h`, the period of `W` against the theta kernel at `h` is the sum
of the values of the unfolded function `Y.unfoldStep Y' α Φ W` at `γ h`, over `γ` in
`Y'.ratBessel \ V'.Γ`. Here `γ` is the inverse of the chosen representative of a left coset `q`. -/
lemma hasSum_unfoldStep (hW : Y.IsEquivariant W) (h : G E ε') :
    HasSum (fun q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ ↦
        Y.unfoldStep Y' α Φ W ((q.out : G E ε')⁻¹ * h))
      (∫ r : Y.besselGroup, W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ)
        ∂Y.besselMeasure) := by
  -- Only the translates of `𝒞` survive, and the integrals of the terms of one translate add up to
  -- one value of the unfolded function.
  obtain ⟨e, he⟩ := exists_equiv_agreeingTranslates Y' α Φ hW
  have all_translates : HasSum
      (fun w : Y.agreeingTranslates Y' ↦ ∫ r, classTerm α Φ W w.1 h r ∂Y.besselMeasure)
      (∫ r, W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) ∂Y.besselMeasure) :=
    (hasSum_integral_classTerm Y' α Φ hW (by simp) h _).summable.hasSum_iff.2
      (tsum_agreeingTranslates Y' α Φ hW h)
  have one_translate (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) : HasSum
      (fun w : Y.agreeingClasses Y' 0 ↦ ∫ r, classTerm α Φ W (e (q, w)).1 h r ∂Y.besselMeasure)
      (Y.unfoldStep Y' α Φ W ((q.out : G E ε')⁻¹ * h)) := by
    simp only [he]
    exact (hasSum_integral_classTerm Y' α Φ hW (by simp) _ _).summable.hasSum_iff.2
      (tsum_integral_classTerm_agreeingClasses Y' α Φ hW _)
  exact (e.hasSum_iff.2 all_translates).prod_fiberwise one_translate

include Y' in
/-- For the weights `d = 0`, an equivariant `W` and a rapidly decreasing `y`, the sums of the norms
of the terms times `y h` are bounded, uniformly in `h`, `r` and the set of classes. -/
lemma exists_tsum_enorm_classTerm_mul_le (hW : Y.IsEquivariant W) {y : G E ε' → ℂ}
    (hy_rapid : V'.IsRapid y) :
    ∃ c : NNReal, ∀ (h : G E ε') (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0))
      (r : Y.besselGroup), ∑' w : S, ‖classTerm α Φ W w.1 h r * y h‖ₑ ≤ c := by
  -- With `h` reduced, the growth of the Weil representation is absorbed by the decay of `y`.
  obtain ⟨a, ha⟩ := exists_tsum_enorm_classTerm_le Y' α Φ hW (d := 0) (by simp)
  obtain ⟨B, reduce⟩ : ∃ B : ℕ, ∀ h : G E ε', ∃ δ ∈ V'.Γ,
      ‖pairWeil V V' (α ι) (α ι') (1, δ * h)‖ ≤ 2 ^ B * V'.height h ^ B :=
    ((pairThetaKer V V' (α ι) (α ι')).eventually_exists_norm_omega_le_mul_height_pow 1).exists
  obtain ⟨C, decay⟩ : ∃ C : ℝ, ∀ h : G E ε', ‖y h‖ * V'.height h ^ B ≤ C := hy_rapid B
  refine ⟨(2 ^ B * C).toNNReal * a, fun h S r ↦ ?_⟩
  obtain ⟨δ, δ_rat, hδ⟩ := reduce h
  set ρ : 𝒮 (V.hom V') →L[ℂ] 𝒮 (V.hom V') := pairWeil V V' (α ι) (α ι') (1, δ * h)
  have absorb : ‖y h‖ * ‖ρ‖ ≤ 2 ^ B * C := by grw [hδ, mul_left_comm, decay]
  calc _ = (∑' w : S, ‖classTerm α Φ W w.1 h r‖ₑ) * ‖y h‖ₑ := by
        simp only [enorm_mul, ENNReal.tsum_mul_right]
    _ ≤ ‖ρ‖ₑ * a * ‖y h‖ₑ := by grw [ha h ⟨δ, δ_rat, nofun⟩ S r]
    _ = .ofReal (‖y h‖ * ‖ρ‖) * a := by
        rw [ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, mul_right_comm, mul_comm ‖ρ‖ₑ]
    _ ≤ .ofReal (2 ^ B * C) * a := by gcongr

/-- For an equivariant `W` and a rapidly decreasing `y`, the sum over `γ` in `Y'.ratBessel \ V'.Γ`
of the norms of `Y.unfoldStep Y' α Φ W (γ h) * y h` is at most a constant, independent of `h`, times
the (finite) total mass of `Y.besselMeasure`. -/
lemma exists_tsum_enorm_unfoldStep_mul_le (hW : Y.IsEquivariant W) {y : G E ε' → ℂ}
    (hy_rapid : V'.IsRapid y) :
    ∃ c : NNReal, ∀ h : G E ε', ∑' q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ,
      ‖Y.unfoldStep Y' α Φ W ((q.out : G E ε')⁻¹ * h) * y h‖ₑ ≤ c * Y.besselMeasure univ := by
  -- Each value is a sum of integrals of terms over one translate of `𝒞`.
  have term_cont (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) : Continuous ↿(classTerm α Φ W w) :=
    continuous_classTerm Y' α Φ hW (by simp) w
  obtain ⟨c, bound⟩ : ∃ c : NNReal, ∀ (h : G E ε') (S : Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0))
      (r : Y.besselGroup), ∑' w : S, ‖classTerm α Φ W w.1 h r * y h‖ₑ ≤ c :=
    exists_tsum_enorm_classTerm_mul_le Y' α Φ hW hy_rapid
  obtain ⟨e, he⟩ := exists_equiv_agreeingTranslates Y' α Φ hW
  refine ⟨c, fun h ↦ ?_⟩
  calc _ ≤ ∑' (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) (w : Y.agreeingClasses Y' 0),
          ‖∫ r, classTerm α Φ W (e (q, w)).1 h r * y h ∂Y.besselMeasure‖ₑ := by
        simp only [he, ← tsum_integral_classTerm_agreeingClasses Y' α Φ hW, ← tsum_mul_right,
          integral_mul_const]
        exact ENNReal.tsum_le_tsum fun q ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' w : Y.agreeingTranslates Y',
          ‖∫ r, classTerm α Φ W w.1 h r * y h ∂Y.besselMeasure‖ₑ := by
        rw [← e.tsum_eq, ENNReal.tsum_prod']
    _ ≤ ∑' w : Y.agreeingTranslates Y',
          ∫⁻ r, ‖classTerm α Φ W w.1 h r * y h‖ₑ ∂Y.besselMeasure :=
        ENNReal.tsum_le_tsum fun w ↦ enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ r, ∑' w : Y.agreeingTranslates Y',
          ‖classTerm α Φ W w.1 h r * y h‖ₑ ∂Y.besselMeasure := by
        rw [lintegral_tsum (by fun_prop)]
    _ ≤ ∫⁻ _, c ∂Y.besselMeasure := lintegral_mono (bound h _)
    _ = c * Y.besselMeasure univ := lintegral_const _

/-- Let `W` be a `ψ_U`-equivariant function on the Bessel group of `Y`, and let `y` be an
automorphic function of rapid decay on `U(V')(𝔸)`. Write `Y.unfoldStep Y' α Φ W h` for the integral
of `W r * Y.constTermAtStringMap Y' α Φ r h` over the Bessel group of `Y` modulo its rational
points. Then `h ↦ Y.unfoldStep Y' α Φ W h * y h` is integrable over `Y'.ratBessel \ U(V')(𝔸)`, and
its integral there equals `∫ W(r) ∫ θ(ω(r, h) Φ) y(h) dh dr`, where `ω = twistedPairWeil α`, `h`
runs over `V'.Γ \ U(V')(𝔸)` and `r` over the Bessel group of `Y` modulo its rational points. -/
lemma integral_besselGroup_unfold (hW : Y.IsEquivariant W) {y : G E ε' → ℂ}
    (hy : V'.IsAutomorphic y) (hy_rapid : V'.IsRapid y) :
    Integrable (fun h : G E ε' ↦ Y.unfoldStep Y' α Φ W h * y h) Y'.ratBessel.quotMeasure ∧
    ∫ r : Y.besselGroup, W r * ∫ h : G E ε',
        θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) * y h ∂V'.quotMeasure ∂Y.besselMeasure =
      ∫ h : G E ε', Y.unfoldStep Y' α Φ W h * y h ∂Y'.ratBessel.quotMeasure := by
  -- Exchange the two integrals, write the period over the Bessel group as a sum over cosets
  -- (`hasSum_unfoldStep`), and unfold that sum.
  have y_cont : Continuous y := hy.continuous
  have unfold_cont : Continuous (Y.unfoldStep Y' α Φ W) := continuous_unfoldStep hW
  let k (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) (h : G E ε') : ℂ :=
    Y.unfoldStep Y' α Φ W ((q.out : G E ε')⁻¹ * h) * y h
  have k_meas (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) : Measurable (k q) :=
    Continuous.measurable (by fun_prop)
  have k_sum (h : G E ε') : ∑' q : (univ : Set (V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ)), k q h =
      (∫ r : Y.besselGroup, W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ)
        ∂Y.besselMeasure) * y h :=
    (tsum_univ fun q ↦ k q h).trans ((hasSum_unfoldStep Y' α Φ hW h).mul_right (y h)).tsum_eq
  -- The term of a coset may be read at any representative, so `V'.Γ` permutes the terms.
  have k_eq (δ : V'.Γ) (h : G E ε') :
      k δ h = Y.unfoldStep Y' α Φ W ((δ : G E ε')⁻¹ * h) * y h := by
    have h_mem : (δ : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ).out⁻¹ * δ ∈
        Y'.ratBessel.subgroupOf V'.Γ := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [k, mul_assoc] using
      congrArg (· * y h) (unfoldStep_rat_mul _ h_mem ((δ : G E ε')⁻¹ * h))
  have k_smul (δ : V'.Γ) (q : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) (h : G E ε') :
      k (δ • q) (δ * h) = k q h := by
    rw [← Quotient.mk_smul_out, k_eq]
    simp [k, mul_assoc, hy.rat_mul _ δ.2]
  have k_one : k (1 : V'.Γ) = fun h : G E ε' ↦ Y.unfoldStep Y' α Φ W h * y h :=
    funext fun h ↦ by simpa using k_eq 1 h
  have stab_eq : (stabilizer V'.Γ ((1 : V'.Γ) : V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ)).map
      V'.Γ.subtype = Y'.ratBessel := by
    rw [stabilizer_quotient, subgroupOf_map_subtype, inf_of_le_left inf_le_left]
  have finite : ∫⁻ h, ∑' q, ‖k q h‖ₑ ∂V'.quotMeasure < ∞ := by
    obtain ⟨c, bound⟩ := exists_tsum_enorm_unfoldStep_mul_le Y' α Φ hW hy_rapid
    grw [bound]
    -- `withDensity_apply` would unfold the quotient measure, whose total mass is finite.
    simp [mul_lt_top_iff, -withDensity_apply]
  have : Countable (V'.Γ ⧸ Y'.ratBessel.subgroupOf V'.Γ) := Quotient.countable
  obtain ⟨integrable, unfolded, -⟩ := integral_tsum_orbit_of_lt_top_or_integrable (μ := volume)
    (D := univ)
    val_injective V'.Γ.range_subtype k_meas k_smul stab_eq (fun q ↦ by simp [orbit_eq_univ])
    (.inl finite)
  simp only [k_sum, k_one] at integrable unfolded
  have product_integrable : Integrable (Function.uncurry fun h (r : Y.besselGroup) ↦
      W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) * y h)
      (V'.quotMeasure.prod Y.besselMeasure) := by
    have W_cont : Continuous W := hW.continuous
    obtain ⟨c, bound⟩ := exists_tsum_enorm_classTerm_mul_le Y' α Φ hW hy_rapid
    refine ⟨(Continuous.measurable (by fun_prop)).aestronglyMeasurable,
      .of_bounded_enorm (C := c) coe_ne_top (.of_forall fun ⟨h, r⟩ ↦ ?_)⟩
    rw [Function.uncurry_apply_pair, ← tsum_classTerm Y' α Φ, ← tsum_mul_right]
    exact enorm_tsum_le_tsum_enorm.trans (bound h univ r)
  have fubini : ∫ r : Y.besselGroup, W r * ∫ h : G E ε',
        θ (V.hom V') (twistedPairWeil α (r.1, h) Φ) * y h ∂V'.quotMeasure ∂Y.besselMeasure =
      ∫ h : G E ε', (∫ r : Y.besselGroup, W r * θ (V.hom V') (twistedPairWeil α (r.1, h) Φ)
        ∂Y.besselMeasure) * y h ∂V'.quotMeasure := by
    simp only [← integral_const_mul, ← mul_assoc, ← integral_integral_swap product_integrable,
      integral_mul_const]
  exact ⟨integrable, fubini.trans unfolded⟩

end New.Grading

end
