import Lib.ClassField.Places.DecompositionCyclotomic
import Lib.PadicHodge.PeriodRings.CrystallineRings

/-!
# The cyclotomic action on μ, the period t, and the de Rham field B_dR

This file studies the Galois and Frobenius actions on Fontaine's period rings for `ℂ_[p]`. We write
A_inf = `New.Period.Ainf` (Witt vectors of `OFlat`, the tilt of the integers of `ℂ_[p]`),
ε = `New.Period.epsTilt` (a compatible system of `p`-power roots of unity in the tilt), μ = [ε] − 1,
ξ for the generator of the kernel of θ, φ for Frobenius (`New.Period.frobEnd`) and χ for the
cyclotomic character `New.cyclotomicGp`. Let B_dR⁺ = `New.Period.BdRPlus`, the ξ-adic completion of
B⁺ = `New.Period.BPlus`. The fraction field B_dR of B_dR⁺ contains B = B⁺[1/μ] and Q̄_p
equivariantly.

## Main definitions and results

* `New.Lift.mu_sq_dvd_smul_mu_sub`: in `New.Period.Ainf`, the Witt vectors of the tilt of the
  integers of `ℂ_[p]`, an element `g` of the Galois group `New.Gp p` sends `μ = [ε] - 1` to `χ(g) μ`
  modulo `μ ^ 2`. Here `ε` is `New.Period.epsTilt` and `χ` is the cyclotomic character. The
  divisibility `μ ^ 2 ∣ g μ - χ(g) μ` holds in `A_inf` itself; the proof checks it modulo every
  power of the ideal `(p, ξ)`, where `ξ` generates the kernel of Fontaine's map `θ`.
* `New.Period.exists_tPeriod`: some unit multiple `t` of `p μ` has `φ t = p t` and `g t = χ(g) t`.
* `New.Period.BdR`: the fraction field of B_dR⁺; G_p acts on it and B embeds in it equivariantly.
* An embedding of Q̄_p in B_dR⁺, got by lifting along θ since Q̄_p is formally étale over ℚ_p;
  `New.Period.thetaBdR_algebraMap_padicAlgCl` says it is a section of θ,
  `New.Period.BdR.smul_algebraMap_padicAlgCl` that it is G_p-equivariant.
* `New.Period.Bmax.fundamental_sequence_surjective`: (φ − 1, inclusion) maps B onto
  B × B_dR / B_dR⁺, the surjectivity in the fundamental exact sequence.

Notions from other files:
* `New.Period.Amax`: The ring A, the p-adic completion of A_inf[ξ/p]; B⁺ = A[1/p].
* `New.Period.mu`, `New.Period.tau`, `New.Period.xi`: The elements μ = [ε] − 1, τ = [ε^{1/p}] − 1
  and ξ = Σ_{0 ≤ i < p} [ε^{1/p}]^i of A_inf; ξτ = μ and φ(τ) = μ.

## Relation to the literature

Known result: Fontaine's period rings and the fundamental exact sequence. Here Colmez's B_max
replaces B_cris and the period t is built without logarithms. The part of Fontaine's regularity that
is used, namely that the invariants of the fraction field of B already lie in B, is proved in
`Lib.PadicHodge.Crystalline.Regularity` (`New.Period.fontaine_regularity`). Source: P. Colmez,
Théorie d'Iwasawa des représentations de de Rham d'un corps local, Ann. of Math. 148 (1998),
III.2-III.3; J.-M. Fontaine, Le corps des périodes p-adiques, Astérisque 223 (1994); X. Caruso, An
introduction to p-adic period rings (2019), §3.
-/

noncomputable section

/-! ## The action of G_p on μ modulo μ² -/

namespace New.Lift

open Period Ideal WittVector SModEq Ainf

variable {p : ℕ} [ThePrime p]

@[simp]
lemma iterate_frobEnd_teichmuller (x : OFlat) (n : ℕ) :
    frobEnd^[n] (teichmuller p x) = teichmuller p x ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ, pow_mul]

/-- If `ξ` divides `x - y` in `A_inf`, then `x ^ p ^ m - y ^ p ^ m` lies in the `m`-th power of the
ideal `(p, ξ)`. -/
lemma pow_p_pow_sub_mem_of_xi_dvd {x y : Ainf} (h_xi_dvd : xi ∣ x - y) (m : ℕ) :
    x ^ p ^ m - y ^ p ^ m ∈ span {↑p, xi} ^ m := by
  have h_mod : x ≡ y [SMOD span {(p : Ainf), xi}] :=
    SModEq.sub_mem.mpr (mem_of_dvd _ h_xi_dvd (subset_span (by simp)))
  have h_pow : x ^ p ^ m ≡ y ^ p ^ m [SMOD span {↑p, xi} ^ (m + 1)] :=
    pow_pow_add_one (subset_span (by simp)) h_mod m
  exact Ideal.pow_le_pow_right m.le_succ (SModEq.sub_mem.mp h_pow)

/-- Let `g` be an element of the Galois group `G_p` and `χ(g)` in `ℤ_[p]ˣ` its cyclotomic
character. Then `μ ^ 2` divides `g μ - χ(g) μ` in `A_inf`, where `μ = [ε] - 1`: the element `g`
sends `μ` to `χ(g) μ` modulo `μ ^ 2`. -/
lemma mu_sq_dvd_smul_mu_sub (g : Gp p) : mu ^ 2 ∣ g • mu - (cyclotomicGp g : ℤ_[p]) • mu := by
  -- As `p` does not divide `μ ^ 2`, it suffices (`dvd_of_forall_exists_sub_mem_span_pow`) to prove
  -- the divisibility modulo `(p, ξ) ^ m` for every `m`.
  have hp_not_dvd : ¬(p : Ainf) ∣ mu ^ 2 := by
    simp [Witt.p_dvd_iff, -constantCoeff_apply, constantCoeff_mu_ne_zero]
  refine dvd_of_forall_exists_sub_mem_span_pow prime_p.not_isUnit prime_xi.not_isUnit hp_not_dvd
    fun m ↦ ?_
  -- Let `u = [ε^{1/p^m}]` and let `a` be the cyclotomic character of `g` modulo `p ^ m`.
  let u : Ainf := teichmuller p ((frobeniusEquiv _ p).symm^[m] epsTilt)
  let a : ℕ := (cyclotomicCharMod ℂ_[p] (p ^ m) g : ZMod (p ^ m)).val
  have hu : u ^ p ^ m = 1 + mu := by simp [u, mu, ← map_pow]
  -- `θ u` is a `p ^ m`-th root of unity, as `u ^ p ^ m = 1 + μ` and `θ μ = 0`; `g` acts on it as
  -- the `a`-th power, and `ker θ = (ξ)`.
  have h_root : theta u ^ p ^ m = 1 := by
    simp [← map_pow, hu, theta_eq_zero_iff_xi_dvd.mpr (Dvd.intro tau xi_mul_tau)]
  have h_act : g • (theta u : ℂ_[p]) = (theta u : ℂ_[p]) ^ a :=
    smul_eq_pow_cyclotomicCharMod g (mod_cast h_root)
  have h_xi : xi ∣ g • u - u ^ a := by
    simpa [← theta_eq_zero_iff_xi_dvd, u, Subtype.ext_iff, sub_eq_zero] using h_act
  have h_pow : 1 + g • mu - (1 + mu) ^ a ∈ span {↑p, xi} ^ m := by
    simpa [← smul_pow', pow_right_comm u a, hu] using pow_p_pow_sub_mem_of_xi_dvd h_xi m
  -- The cyclotomic characters of the algebraic closure and of its completion agree.
  have h_chi : (p : ℤ_[p]) ^ m ∣ (cyclotomicGp g).val - a := by
    rw [cyclotomicGp,
      cyclotomicChar_eq_of_equivariant p (j := algebraMap _ ℂ_[p]) fun x ↦ (smul_coe_Cp g x).symm]
    exact (pow_dvd_cyclotomicChar_sub_iff m).mpr zmod_eq_natCast_val
  have h_lin : (p : Ainf) ^ m ∣ (cyclotomicGp g : ℤ_[p]) • mu - a * mu := by
    simpa [sub_mul, Algebra.smul_def] using (map_dvd (algebraMap _ Ainf) h_chi).mul_right mu
  -- Binomial expansion: `(1 + μ) ^ a = 1 + a μ + μ² x`.
  obtain ⟨x, hx⟩ : mu ^ 2 ∣ (1 + mu) ^ a - mu * a - 1 := by
    simpa using sq_dvd_add_pow_sub_sub mu 1 a
  have h_eq : g • mu - (cyclotomicGp g : ℤ_[p]) • mu - mu ^ 2 * x =
      (1 + g • mu - (1 + mu) ^ a) - ((cyclotomicGp g : ℤ_[p]) • mu - a * mu) := by
    linear_combination hx
  use x
  rw [h_eq]
  exact sub_mem h_pow (mem_of_dvd _ h_lin (pow_mem_pow (subset_span (by simp)) m))

end New.Lift

namespace New.Period

/-!
## The period t with φt = pt and gt = χ(g)t

The period is constructed without logarithms, in `New.Period.Amax`, the `p`-adic completion of
`A_inf[ξ / p]`.
-/

section PeriodT

open Amax Algebra algebraMap NeZero

variable {p : ℕ} [ThePrime p]

/-- Let `u` be an element of `Amax` divisible by `p`. Then for every `w` the equation
`c - u φ(c) = w` has a solution `c` in `Amax`, where `φ` is the Frobenius `frobEnd`. -/
lemma Amax.exists_sub_mul_frobEnd_eq {u : Amax} (hp_dvd : (p : Amax) ∣ u) (w : Amax) :
    ∃ c : Amax, c - u * frobEnd c = w := by
  -- `c ↦ c - u * φ c` is the identity modulo `p`, so it is onto by successive approximation
  let f : Amax →+ Amax := .id Amax - u • frobEnd.toAddMonoidHom
  have h_step (v : Amax) : ∃ n y : Amax, v = f n + (p : ℤ) • y := by
    obtain ⟨y, hy⟩ : (p : Amax) ∣ u * frobEnd v := hp_dvd.mul_right _
    exact ⟨v, y, by simp [f, ← hy]⟩
  simpa [f] using mem_range_of_approx f (map_zsmul f p) id h_step w

/-- The Frobenius `frobEnd` of `Amax` is the action of the Frobenius element `(ofAdd 1, 1)` of
`FrobGal`. -/
private lemma frobEnd_eq_smul (x : Amax (p := p)) :
    frobEnd x = ((Multiplicative.ofAdd 1, 1) : FrobGal) • x :=
  rfl

/-- There is an element `t` of Colmez's period ring `Amax` (the p-adic completion of
`A_inf[X]/(pX − ξ)`) that is a unit multiple of `μ p`, where `μ = [ε] − 1` is the element `mu` of
`A_inf`. It satisfies `φ t = p t` and `g t = χ(g) t` for all `g` in `G_p = Gal(Q̄_p/Q_p)`, where `χ`
is the p-adic cyclotomic character.

The element `t` plays the role of Fontaine's period `t`, up to the factor `p`. -/
lemma exists_tPeriod : ∃ t : Amax,
    Associated (mu * p : Amax) t ∧
    frobEnd t = p * t ∧
    ∀ g : Gp p, g • t = (cyclotomicGp g : ℤ_[p]) • t := by
  -- Write `φ ξ = p u` with `u` a unit and `φ ξ - p = μ w`. Then `φ μ = p u μ`, and
  -- `t = μ (p + μ c)` works, where `c` solves `c - p u² φ c = w`.
  set μ : Amax := ↑mu with hμ
  obtain ⟨u, hu⟩ : ∃ u : Amaxˣ, p * (u : Amax) = frobEnd xi := associated_p_frobEnd_xi
  -- apply `φ` to `τ ∣ ξ - p`, with `φ τ = μ`
  obtain ⟨w, hw⟩ : μ ∣ p * u - p := by
    simpa [hu, hμ, -isUnit_map_iff] using
      map_dvd (algebraMap Ainf Amax) (map_dvd frobEnd tau_dvd_xi_sub_p)
  obtain ⟨c, hc⟩ : ∃ c : Amax, c - p * u ^ 2 * frobEnd c = w :=
    exists_sub_mul_frobEnd_eq (dvd_mul_right _ _) w
  have phi_μ : frobEnd μ = p * u * μ := by
    rw [hu, hμ, frobEnd_algebraMap, ← map_mul, ← frobEnd_tau, ← map_mul, xi_mul_tau, frobEnd_tau]
  let t : Amax := μ * (p + μ * c)
  -- expand `t` with `μ w = p u - p` and `c = w + p u² φ c`
  have t_eq : μ * p * (u + μ * u ^ 2 * frobEnd c) = t := by
    linear_combination μ * hw - μ ^ 2 * hc
  -- `φ t = p u μ (p + p u μ φ c)` is `p` times the left side of `t_eq`
  have phi_t : frobEnd t = p * t := by
    rw [map_mul, map_add, map_mul, map_natCast, phi_μ, ← t_eq]
    ring
  -- `p ∣ ξ ∣ μ` in `Amax`, so the last factor in `t_eq` is the unit `u` modulo `p`
  have h_p_dvd : (p : Amax) ∣ u + μ * u ^ 2 * frobEnd c - u := by
    simp [μ, ← xi_mul_tau, mul_assoc]
  have h_unit : IsUnit (u + μ * u ^ 2 * frobEnd c) := isUnit_of_dvd_sub u.isUnit h_p_dvd
  refine ⟨t, ⟨h_unit.unit, t_eq⟩, phi_t, fun g ↦ ?_⟩
  -- `δ = g t - χ(g) t` is divisible by every `p ^ n μ²`, so it vanishes
  set χ : ℤ_[p] := ↑(cyclotomicGp g)
  set δ : Amax := g • t - χ • t with hδ
  have phi_δ : frobEnd δ = p * δ := by
    have phi_smul : frobEnd (χ • t) = χ • frobEnd t := by simp only [frobEnd_eq_smul, smul_comm]
    simp [hδ, ← smul_frobEnd, phi_smul, phi_t, mul_sub]
  have h_dvd (n : ℕ) : p ^ n * μ ^ 2 ∣ δ := by
    induction n with
    | zero =>
      -- `g μ = μ² d + χ(g) μ` and `t = μ (p + μ c)`; expand `g t - χ(g) t`
      obtain ⟨d, hd⟩ : mu ^ 2 ∣ g • mu - χ • mu := Lift.mu_sq_dvd_smul_mu_sub g
      have h_gμ : g • μ = μ ^ 2 * d + algebraMap ℤ_[p] Amax χ * μ := by
        simp [μ, χ, eq_add_of_sub_eq hd, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      have h_gt : g • t = g • μ * (p + g • μ * g • c) := by simp [t, smul_mul', smul_add]
      refine ⟨p * d + (algebraMap ℤ_[p] Amax χ + μ * d) ^ 2 * g • c - χ • c, ?_⟩
      rw [hδ, h_gt, h_gμ, Algebra.smul_def χ c, Algebra.smul_def χ t]
      ring
    | succ n ih =>
      -- applying `φ` to `δ = p ^ n μ² z` gives `p δ = p ^ n (p u μ)² φ z`; cancel `p`
      obtain ⟨z, hz⟩ := ih
      refine ⟨u ^ 2 * frobEnd z, mul_left_cancel₀ (ne (p : Amax)) ?_⟩
      rw [← phi_δ, hz, map_mul, map_mul, map_pow, map_pow, map_natCast, phi_μ]
      ring
  exact eq_of_forall_pow_dvd_sub p fun n ↦ dvd_of_mul_right_dvd (h_dvd n)

/-- A chosen element `t` of `Amax` with the three properties of `exists_tPeriod`. These properties
are unchanged when `t` is multiplied by a unit of `ℤ_[p]`, so they do not fix a normalisation. -/
noncomputable def tPeriodAmax : Amax := exists_tPeriod.choose

/-- In Colmez's ring `Amax` (A_max), the product of μ = [ε] − 1 (the Teichmüller lift of ε minus
one) with p is associated to the chosen period `tPeriodAmax`. That is, `mu * p` equals `tPeriodAmax`
times a unit of `Amax`. -/
lemma associated_mu_mul_p_tPeriodAmax : Associated (mu * p : Amax) tPeriodAmax :=
  exists_tPeriod.choose_spec.1

lemma frobEnd_tPeriodAmax : frobEnd tPeriodAmax = p * tPeriodAmax := by
  obtain ⟨-, h_frob, -⟩ := (exists_tPeriod (p := p)).choose_spec
  exact h_frob

/-- For every `g` in the absolute Galois group G_p of Q_p, `g` acts on the chosen period
`tPeriodAmax` in `Amax` by multiplication by χ(`g`) ∈ ℤ_p, where χ = `cyclotomicGp` is the p-adic
cyclotomic character. -/
lemma smul_tPeriodAmax (g : Gp p) : g • tPeriodAmax = (cyclotomicGp g : ℤ_[p]) • tPeriodAmax := by
  obtain ⟨-, -, h_smul⟩ := (exists_tPeriod (p := p)).choose_spec
  exact h_smul g

/-- The image of `tPeriodAmax` in `B_dR⁺`. It plays the role of `p` times Fontaine's period `t`. -/
noncomputable def tPeriod : BdRPlus := algebraMap Amax BdRPlus tPeriodAmax

lemma tPeriod_def : tPeriod = algebraMap Amax BdRPlus tPeriodAmax := rfl

end PeriodT

/-!
## The field B_dR, the embedding of Q̄_p, and the fundamental sequence

The de Rham period field and its relation to the crystalline ring. Notation:
B⁺ = `New.Period.BPlus`, B = B⁺[1/μ] = `New.Period.Bmax`, B_dR⁺ = `New.Period.BdRPlus` (the ξ-adic
completion of B⁺), with θ : B_dR⁺ → ℂ_p (`New.Period.thetaBdR`) and the Frobenius φ on B
(`New.Period.frobEnd`).
-/

section BdR

open Ideal MulSemiringAction nonZeroDivisors AdicCompletion IsLocalization Away BdRPlus Amax Algebra
  FormallySmooth IsScalarTower BPlus NeZero IsFractionRing algebraMap

variable {p : ℕ} [ThePrime p]
  {R : Type*} [CommRing R] [SMul (Gp p) R] [Algebra R BPlus] [SMulDistribClass (Gp p) R BPlus]
  {S : Type*} [CommRing S] [SMul R S]

instance : SMulCommClass FrobGal ℚ_[p] Bmax where
  smul_comm g := map_smul ((toAlgHom ℤ_[p] Bmax g).extendScalarsOfIsLocalization ℚ_[p] ℤ_[p]⁰)

/-! ### The Galois action on B_dR⁺ and the field B_dR -/

/-- `G_p` acts on `B_dR⁺`. -/
instance actBdRPlus : MulSemiringAction (Gp p) BdRPlus := by
  -- `g` keeps the ideal `(ξ) = ker θ` of `BPlus`, so it extends to the completion.
  apply actionOfHoms _ fun g ↦
    adicMap (toRingHom _ _ g) (by simp [mem_span_singleton, ↓← thetaBPlus_eq_zero_iff])
  -- The two laws are checked on classes of Cauchy sequences, modulo each power of `ξ`.
  · exact DFunLike.ext' (map_ext _ fun x ↦ ext_evalₐ (by simp))
  · exact fun a b ↦ DFunLike.ext' (map_ext _ fun x ↦ ext_evalₐ (by simp [mul_smul]))

instance : SMulDistribClass (Gp p) R BdRPlus :=
  smulDistribClass_of_tower fun _ : BPlus ↦ by apply adicMap_algebraMap

/-- The de Rham period field B_dR, defined as the fraction field of the ring B_dR⁺. -/
@[instance_reducible]
def BdR : Type := FractionRing BdRPlus
  deriving Field

variable [Algebra R BdRPlus] [Algebra S BdRPlus] [IsScalarTower R S BdRPlus]
  [FaithfulSMul R BdRPlus] in
deriving instance Algebra R, IsScalarTower R S, IsFractionRing BdRPlus, FaithfulSMul R for @BdR p _

instance : CharZero BdR := charZero_of_charZero ℚ_[p] _

/-- `G_p` acts on `B_dR`. -/
instance actBdR : MulSemiringAction (Gp p) BdR := mulSemiringAction _ BdRPlus _

instance : SMulDistribClass (Gp p) R BdR := smulDistribClass_of_tower fun _ : BdRPlus ↦ by simp

/-- `B = B⁺[1/μ]` maps to `B_dR`, since `μ` is nonzero in the field `B_dR`. -/
instance : Algebra Bmax BdR :=
  (Away.lift _ ((coe_eq_zero_iff ..).ne.mpr mu_ne_zero).isUnit).toAlgebra

instance : IsScalarTower R Bmax BdR := of_algebraMap_eq fun _ ↦ .symm (lift_eq _ _)

instance : FaithfulSMul Bmax BdR :=
  .of_injective (ofId Bmax BdR)
    ((lift_injective_iff _).mpr (by simp [injective_BPlus_Bmax.eq_iff]))

attribute [local instance] FormallyEtale.of_isSeparable

/-- The embedding of `Q̄_p` in `B_dR⁺`: `Q̄_p` is formally étale over `ℚ_p`, so its map to
`B⁺/ξ ≃ ℂ_p` lifts to the `ξ`-adic completion `B_dR⁺`. -/
instance : Algebra (PadicAlgCl p) BdRPlus :=
  (Exists.choose
    (exists_adicCompletionEvalOneₐ_comp_eq (thetaEquiv.symm.toAlgHom.comp (algHom ..))) :
    _ →ₐ[ℚ_[p]] BdRPlus).toAlgebra

instance : IsScalarTower ℤ_[p] (PadicAlgCl p) BdRPlus := to₁₃₄ _ ℚ_[p] ..

/-- In B_dR⁺ the period t (`tPeriod`) equals ξ times a unit.

This is Fontaine's result that the period t is a uniformiser of B_dR^+, in the form that t and ξ
agree up to a unit. -/
lemma BdRPlus.associated_xi_tPeriod : Associated (xi : BdRPlus) tPeriod := by
  classical
  -- `tPeriod` is associated to `μ * p = ξ * τ * p`, and `τ`, `p` are units of `BdRPlus` since
  -- `thetaBdR` does not kill them.
  have h_xi : Associated (xi : BdRPlus) (algebraMap Amax BdRPlus (mu * p)) := by
    simp [associated_mul_isUnit_right_iff, ne, ← xi_mul_tau, ← IsScalarTower.algebraMap_apply,
      -p_mul_X]
  exact h_xi.trans (associated_mu_mul_p_tPeriodAmax.map _)

/-- For every `g` in the absolute Galois group G_p of Q_p, `g` acts on `tPeriod` by multiplication
by χ(`g`) ∈ ℤ_p, where χ = `cyclotomicGp` is the p-adic cyclotomic character. Here `tPeriod` is the
image of `tPeriodAmax` in B_dR⁺, which plays the role of p times Fontaine's t. -/
lemma smul_tPeriod (g : Gp p) : g • tPeriod = (cyclotomicGp g : ℤ_[p]) • tPeriod := by
  simp [tPeriod_def, smul_tPeriodAmax, smul_def, ← IsScalarTower.algebraMap_apply]

/-! ### θ, the embedding of Q̄_p, and the fundamental sequence -/

/-- For x in Q̄_p, the map θ: B_dR⁺ → ℂ_p sends the image of x in B_dR⁺ to x itself, viewed in
ℂ_p. -/
@[simp]
lemma thetaBdR_algebraMap_padicAlgCl (x : PadicAlgCl p) : thetaBdR x = .coe' x :=
  thetaEquiv.eq_symm_apply.mp
    (AlgHom.congr_fun (exists_adicCompletionEvalOneₐ_comp_eq _).choose_spec x)

@[simp]
lemma thetaBdR_smul (g : Gp p) (x : BdRPlus) : thetaBdR (g • x) = g • thetaBdR x := by
  -- Modulo `xi`, which `thetaBdR` kills, `p ^ n * x` is an element `r` of `Ainf`, and on `Ainf` the
  -- map is equivariant. So both sides agree after multiplying by `p ^ n`.
  obtain ⟨n, r, c, h_approx⟩ := x.exists_Ainf_approx 1
  have h_left : p ^ n * thetaBdR (g • x) = g • thetaBdR r := by
    simpa [smul_sub, sub_eq_zero] using congrArg (fun y : BdRPlus ↦ thetaBdR (g • y)) h_approx
  have h_right : p ^ n * g • thetaBdR x = g • thetaBdR r := by
    simpa [smul_sub, sub_eq_zero] using congrArg (fun y : BdRPlus ↦ g • thetaBdR y) h_approx
  simpa [ne] using h_left.trans h_right.symm

instance : SMulDistribClass (Gp p) Bmax BdR := by
  -- two ring maps out of the localisation `Bmax` agree as soon as they agree on `BPlus`
  refine smulDistribClass_of_tower (B := Bmax) (congrFun ?_)
  apply IsLocalization.ext (.powers (mu : BPlus)) <;> simp [← IsScalarTower.algebraMap_apply]

/-- The embedding of Q̄_p in B_dR is G_p-equivariant: g applied to the image of x is the image of
g(x).

This is the G_p-equivariance of the embedding of Q̄_p in B_dR^+ (Caruso; Brinon–Conrad), stated
after passing to the field B_dR. -/
@[simp]
lemma BdR.smul_algebraMap_padicAlgCl (g : Gp p) (x : PadicAlgCl p) : g • (x : BdR) = g x := by
  -- The action of `g` on `BdR` is a `ℚ_[p]`-algebra map, so it restricts to some endomorphism `σ`
  -- of the normal extension `PadicAlgCl p`.
  let act : BdR (p := p) →ₐ[ℚ_[p]] BdR :=
    (toAlgHom ℤ_[p] BdR g).extendScalarsOfIsLocalization ℚ_[p] ℤ_[p]⁰
  let σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := act.restrictNormal (PadicAlgCl p)
  have hσ : (σ x : BdR) = g • (x : BdR) := act.restrictNormal_commutes _ x
  -- This holds already in `BdRPlus`; applying the equivariant map `thetaBdR` gives `σ x = g x`.
  have h_tower : g • ((x : BdRPlus) : BdR) = ((g • (x : BdRPlus) : BdRPlus) : BdR) :=
    smul_algebraMap_eq_algebraMap_smul g (x : BdRPlus)
  have hσ_plus : (σ x : BdRPlus) = g • (x : BdRPlus) := coe_inj.mp (hσ.trans h_tower)
  have hσ_eq : σ x = g x := by simpa using congrArg thetaBdR hσ_plus
  rw [← hσ, hσ_eq]

/-- An element of `A_inf` that divides `μ` becomes a unit in `B = B⁺[1/μ]`. -/
private lemma isUnit_coe_Bmax_of_dvd_mu {a : Ainf} (ha : a ∣ mu) : IsUnit (a : Bmax (p := p)) := by
  simpa only [one_smul] using isUnit_smul_of_dvd_mu 1 ha

/-- For every `β` in `B_dR` there are `y` in `B` and `x` in `B_dR⁺` with `x = y - β` in `B_dR`:
every element of `B_dR` is congruent modulo `B_dR⁺` to an element of `B`. -/
lemma Bmax.exists_coe_eq_sub (β : BdR (p := p)) :
    ∃ (y : Bmax) (x : BdRPlus), (x : BdR) = y - β := by
  -- Write `β = x / (ξ ^ k u)` with `u` a unit, and `x / u = y + ξ ^ k x₀` with `y` in `B⁺`.
  obtain ⟨x, z, hz, hβ⟩ := div_surjective BdRPlus β
  obtain ⟨k, u, rfl⟩ := exists_associated_xi_pow (ne_zero hz)
  obtain ⟨y, x₀, h_approx⟩ := (x * ↑u⁻¹).exists_xi_pow_dvd_sub k
  -- As `ξ` is a unit of `B`, the element `y / ξ ^ k`, which equals `β - x₀`, lies in `B`.
  obtain ⟨r, hr⟩ : IsUnit ((xi : Bmax) ^ k) :=
    (isUnit_coe_Bmax_of_dvd_mu (Dvd.intro tau xi_mul_tau)).pow k
  refine ⟨y • ↑r⁻¹, -x₀, ?_⟩
  linear_combination (norm := skip)
    -(hβ - (((r⁻¹ : Bmaxˣ) : Bmax) : BdR) * congrArg (algebraMap BdRPlus BdR) h_approx)
  -- In the field `B_dR` the inverses of `r` and `u` become `(ξ ^ k)⁻¹` and `u⁻¹`, and `ξ ≠ 0`.
  simp [smul_def, Ainf.prime_xi.ne_zero, hr, ← IsScalarTower.algebraMap_apply, sub_eq_zero]
  ring

/-- For every `a` in `B` there is `y` in `B` with `φ y - y = a` whose image in `B_dR` is the image
of some `x` in `B_dR⁺`: the map `φ - 1` sends `B ∩ B_dR⁺` onto `B`. -/
lemma Bmax.exists_frobEnd_sub_eq_and_coe_eq (a : Bmax (p := p)) :
    ∃ (y : Bmax) (x : BdRPlus), frobEnd y - y = a ∧ (x : BdR) = y := by
  -- Write `a = b / μ ^ m` and `p ^ n b = e + p ^ n μ ^ (m + 1) w` with `e` in `A_inf`, `w` in `A`,
  -- so that `a = e / (p ^ n μ ^ m) + μ w`.
  obtain ⟨m, b, hb⟩ : ∃ (m : ℕ) (b : BPlus), a * ((mu : BPlus) : Bmax) ^ m = b :=
    surj (mu : BPlus) a
  obtain ⟨n, e, _, ⟨w, rfl⟩, h_dense⟩ :
      ∃ (n : ℕ) (e : Ainf), ∃ w ∈ amaxImage, p ^ n * b = e + p ^ n * mu ^ (m + 1) * w :=
    b.exists_Ainf_approx 0 (m + 1)
  -- If `e = φ c - ξ ^ m c`, then `φ - 1` sends `c / (p ^ n τ ^ m)` to the first term, because
  -- `φ τ = μ = ξ τ`. If `w = d - φ(ξ) φ(d)`, then it sends `-μ d` to the second: `φ μ = φ(ξ) μ`.
  -- Such `d` exists because `p` divides `φ(ξ)` in `A`.
  obtain ⟨c, rfl⟩ := e.exists_frobEnd_sub_xi_pow_mul_eq m
  obtain ⟨d, rfl⟩ := exists_sub_mul_frobEnd_eq associated_p_frobEnd_xi.dvd w
  -- The denominator `p ^ n τ ^ m` is a unit `s` of `B` and a unit `v` of `B_dR⁺`.
  have h_xi : IsUnit (xi : Bmax) := isUnit_coe_Bmax_of_dvd_mu (Dvd.intro tau xi_mul_tau)
  have h_tau : IsUnit (tau : Bmax) := isUnit_coe_Bmax_of_dvd_mu (Dvd.intro_left xi xi_mul_tau)
  obtain ⟨s, hs⟩ : IsUnit ((p : BPlus) ^ n • (tau : Bmax) ^ m) :=
    (h_tau.pow m).smul (isUnit_p.pow n).unit
  obtain ⟨v, hv⟩ : IsUnit (tau ^ m * p ^ n : BdRPlus) := by simp [ne]
  refine ⟨c • ↑s⁻¹ - mu * d, c • ↑v⁻¹ - mu * d, ?_, ?_⟩
  · -- Multiply by the unit `s ξ ^ m = p ^ n μ ^ m` to clear the denominator.
    apply (s * h_xi.unit ^ m).mul_right_inj.mp
    have h_frob_s : frobEnd (c • ((s : Bmax) * ↑s⁻¹)) = frobEnd (c • (1 : Bmax)) := by
      rw [s.mul_inv]
    have h_xi_s : xi ^ m • c • ((s : Bmax) * ↑s⁻¹) = xi ^ m • c • (1 : Bmax) := by rw [s.mul_inv]
    have hb_p : (p : Bmax) ^ n * (a * ((mu : BPlus) : Bmax) ^ m) = p ^ n * b := by rw [hb]
    linear_combination (norm := skip)
      h_frob_s - h_xi_s - hb_p - congrArg (algebraMap BPlus Bmax) h_dense
    -- In `B` the unit `s` is `p ^ n τ ^ m` and `ξ τ = μ`; what remains is ring arithmetic.
    simp [smul_def, hs, ← xi_mul_tau, ← IsScalarTower.algebraMap_apply, sub_eq_zero]
    ring
  · simp [smul_def, hs, hv, mul_comm, ← IsScalarTower.algebraMap_apply]

/-- Surjectivity in the fundamental exact sequence: for a in B and β in B_dR there is y in B
with φ(y) − y = a and y − β in B_dR⁺. -/
lemma Bmax.fundamental_sequence_surjective (a : Bmax) (β : BdR) :
    ∃ y : Bmax, ∃ x : BdRPlus, frobEnd y - y = a ∧ (x : BdR) = y - β := by
  -- Take `y₀` congruent to `β` and correct `φ y₀ - y₀` by an element `y₁` of `B ∩ B_dR⁺`.
  obtain ⟨y₀, x₀, h₀⟩ := exists_coe_eq_sub β
  obtain ⟨y₁, x₁, h_phi, h₁⟩ := exists_frobEnd_sub_eq_and_coe_eq (a - (frobEnd y₀ - y₀))
  refine ⟨y₀ + y₁, x₀ + x₁, ?_, ?_⟩
  · rw [map_add]
    linear_combination h_phi
  · rw [algebraMap.coe_add, algebraMap.coe_add]
    linear_combination h₀ + h₁

end BdR

end New.Period

end
