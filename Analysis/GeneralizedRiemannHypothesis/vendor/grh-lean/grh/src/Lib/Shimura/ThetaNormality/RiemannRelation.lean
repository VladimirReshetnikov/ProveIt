import Lib.Shimura.ThetaModuli.PELThetaTori

/-!
# Riemann's theta relation and the reduction of theta functions at a valuation

Theta functions `θ_s = x.thetaCoord s` (`s ∈ D.dualTorsion`) of a theta torus
`x : New.ThetaTori.ThetaTorus` and their reduction at a valuation `v` of `ℂ`.

* `New.ThetaTori.ThetaTorus.isCutOutAt_reduction`: under good reduction, the ideal of the reductions
  of all theta vectors `(θ_s z)_s` has the expected ranks and is cut out by the level points.
* `New.ThetaTori.ThetaTorus.riemann_relation`: Riemann's theta relation of degree `D.paddedNorm` in
  one variable.
* `New.ThetaTori.ThetaTorus.exists_forall_valuation_thetaCoord_zero_le`: each `s` is `u + (s - u)`
  with theta constants of largest valuation.
* `New.ThetaTori.ThetaTorus.IsRiemannTuple`, `New.paddingTuple`: the systems of coefficients
  used in Riemann's relation.

Conventions: `x.torsionLift s` is a chosen lift of the torsion class `s`, `x.latticeOver S` the
lattice over a group `S` of classes, `x.intAction a` multiplication by `a ∈ 𝓞 E`, `x.multiplier` the
multiplier χ of the `θ_s`, and e(t) = exp(2πi t); `IsIntegralCoords w p` says that `p` are integral
homogeneous coordinates of a complex vector `w`, one of them a unit.

Notions from other files:
* `New.ThetaTori.ThetaTorus`: a polarised period map to `V`, with reflection matrix `ℓ`, such that
  multiplication by `star a` is adjoint to multiplication by `a ∈ 𝓞 E` for the form
  `x.automorphyForm`. In suitable coordinates `a` acts on `V` diagonally, through the complex
  embeddings of `E`.
* `New.ThetaTori.PeriodMap.thetaCoord`: The theta coordinate `θ_t`, `t ∈ T`: the normalised
  translate (`New.ThetaTori.normalizedShift`) of
  `New.ThetaTori.PeriodMap.exists_generator_thetaSpace` by the chosen lift `a_t` of `t`.
* `New.RealComplexForm.thetaShift` B a: the twisted translation f ↦ (z ↦ exp(−B(a,z) − B(a,a)/2)
  f(z + a)).
* `New.ThetaTori.LatticeForm.thetaNorm`: the supremum over torsion points x of the sizes
  `New.ThetaTori.LatticeForm.sizeAt` v(exp(−B(x,x)/2) f(x)). `New.ThetaTori.HasGoodReduction` asks,
  for an ample type on the lattice L, that this norm be multiplicative, that r > 1 and v(r) = 1, and
  that some N with v(N) = 1 multiply the dual lattice into L.

## Relation to the literature

Known result: Normal generation of sections on abelian varieties, kept under good reduction. Only
degrees that are powers of one integer r are treated, over a rank-one valuation ring of the complex
numbers, where powers of the sup-norm ball of theta functions are the balls and reduction keeps the
ranks. No cohomology or vanishing theorem is used. Source: S. Koizumi, Theta relations and
projective normality of abelian varieties, Amer. J. Math. 98 (1976); T. Sekiguchi, J. Math. Soc.
Japan 29 (1977) for characteristic p; G. Kempf, Multiplication over abelian varieties, Amer. J.
Math. 110 (1988).

Known result: Riemann's theta relations. Here they are stated in one variable for the theta
coordinates of a PEL torus, with multipliers in the ring of integers of a CM field in place of the
matrix with entries ±1/2. They are proved by Schur orthogonality for the theta group. Source: C.-L.
Chai, Riemann's theta formula (2014), Theorem 1.2; A. Nagano, On Riemann type relations for theta
functions on bounded symmetric domains of type I, arXiv 2301.09243 (2023), Theorem 1.1; D. Mumford,
On the equations defining abelian varieties I, Invent. Math. 1 (1966) §3; G. Kempf, Linear systems
on abelian varieties, Amer. J. Math. 111 (1989) 65–94.
-/

noncomputable section

namespace New.ThetaTori.ThetaTorus

open Module Submodule NNReal Variety ThetaNull MvPolynomial Complex Function NumberField Finset
  Fintype thetaSpace Finite LatticeForm PeriodMap

attribute [local instance low] Fintype.ofFinite

variable {V E k K : Type} [FinComplexSpace V]
  {v : Valuation ℂ ℝ≥0} [Field E] [CMBase E]
  {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
  (x : ThetaTorus D g ℓ V) [Fintype K]
  (a : K → 𝓞 E) {μ μ' : K → D.dualTorsion} {w : V} {t : D.dualTorsion} (p : K → 𝓞 E × 𝓞 E)

/-- The ring of integers `𝓞 E` acts on the torsion group `D.dualTorsion`: the action of `𝓞 E` on
adelic torsion classes preserves `D.dualTorsion`. -/
instance : Module (𝓞 E) D.dualTorsion :=
  module ⟨_, by
    -- Move `a` across the form: it becomes `star a`, which preserves the kernel of `torsionClass`.
    rintro a ⟨y⟩ hy
    refine (D.mem_dualTorsion _).mpr fun z hz ↦ ?_
    simpa [xiForm, ↓star_smul] using
      (D.mem_dualTorsion y).mp hy (algebraMap E (𝔸f E) (star a) • z)
        (torsionClass.ker.smul_mem (star a) hz)⟩

/-! ### Systems of coefficients -/

/-- The pairs `p l = (a_l, b_l)` in `𝓞 E` satisfy `∑ ā_l a_l = r` and `∑ ā_l b_l = 0`, where
`r = D.paddedNorm` is the degree attached to the PEL datum `D` and `ā` is the complex conjugate
(`star`). -/
def IsRiemannTuple (D : PEL E) : Prop :=
  ∑ l : K, star (p l).1 * (p l).1 = D.paddedNorm ∧ ∑ l : K, star (p l).1 * (p l).2 = 0

/-- For a Riemann tuple `p` with `p l = (a_l, b_l)`, `∑ ā_l a_l = D.paddedNorm`. -/
lemma IsRiemannTuple.sum_star_fst_mul_fst {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D) :
    ∑ l : K, star (p l).1 * (p l).1 = D.paddedNorm :=
  And.left hp

/-- For a Riemann tuple `p` with `p l = (a_l, b_l)`, `∑ ā_l b_l = 0`. -/
lemma IsRiemannTuple.sum_star_fst_mul_snd {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D) :
    ∑ l : K, star (p l).1 * (p l).2 = 0 :=
  And.right hp

/-- The family of coefficient pairs on two copies of the index set `K`: `(0, b_l)` on the first
copy, where `k l = (a_l, b_l)`, and `p l` on the second. -/
def doubledCoeffs (k : K → 𝓞 E × 𝓞 E) : K ⊕ K → 𝓞 E × 𝓞 E := Sum.elim (fun l ↦ (0, (k l).2)) p

/-! ### Products of theta functions and Riemann's relation -/

/-- The function `z ↦ ∏_k θ_{μ_k}(a_k z + b_k w)` on `V`, where `p k = (a_k, b_k)`, `θ_s` is the
theta coordinate `x.thetaCoord s` and `x.intAction a` is multiplication by `a ∈ 𝓞 E` on `V`. -/
def thetaProduct (μ : K → D.dualTorsion) (w z : V) : ℂ :=
  ∏ k : K, x.thetaCoord (μ k) (x.intAction (p k).1 z + x.intAction (p k).2 w)

/-- Let `p k = (a_k, b_k)` with `∑ ā_k a_k = r` and `∑ ā_k b_k = 0` (`hp`), let `∑ ā_k μ_k = t`
(`ht`), and let `y` lie in the lattice over `D.dualTorsion`. Write `x.thetaProduct p μ w` for the
function `z ↦ ∏_k θ_{μ_k}(a_k z + b_k w)`, where `θ_s` is `x.thetaCoord s`. If the twisted
translation (`New.RealComplexForm.thetaShift`) by `a_k u` sends `θ_{μ_k}` to
`χ(a_k u) e(⟨a_k y, μ_k⟩) θ_{μ'_k}` for every `k`, then the twisted translation by `u` for `r B`
sends `x.thetaProduct p μ w` to `χ(u)^r e(⟨y, t⟩)` times `x.thetaProduct p μ' w`. Here `χ` is
`x.multiplier`, and `e(⟨y, s⟩)` (`riemannPhase`) is `exp(2πi E(y, ·))` of the chosen lift of `s`,
with `E` the Riemann form of `B = x.automorphyForm`, and `r` is `D.paddedNorm`. -/
lemma thetaShift_thetaProduct {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D)
    (ht : ∑ k : K, star (p k).1 • μ k = t) {u y : V} (hy_mem : y ∈ x.latticeOver D.dualTorsion)
    (h_shift : ∀ k : K, x.automorphyForm.thetaShift (x.intAction (p k).1 u) (x.thetaCoord (μ k)) =
      (x.multiplier (x.intAction (p k).1 u) * x.automorphyForm.riemannPhase (x.intAction (p k).1 y)
        (x.torsionLift (μ k))) • x.thetaCoord (μ' k)) (z : V) :
    (D.paddedNorm • x.automorphyForm).thetaShift u (x.thetaProduct p μ w) z =
      x.multiplier u ^ D.paddedNorm * x.automorphyForm.riemannPhase y (x.torsionLift t) *
        x.thetaProduct p μ' w z := by
  -- Multiply the hypotheses `h_shift k` at `a z + b w` over all `k`; the exponents add up by four
  -- identities. `ht` holds for the lifts only modulo `x.periodLattice`, which pairs integrally
  -- with `y`.
  obtain ⟨hp_norm, hp_orth⟩ := hp
  have h_class : frameTorsionClass g (∑ k, star (p k).1 • ratLift g (μ k)) =
      frameTorsionClass g (ratLift g t) := by
    have h_coe_smul (a : 𝓞 E) (m : D.dualTorsion) :
        ((a • m : D.dualTorsion) : AdelicTorsion E D.Index) = a • (m : AdelicTorsion E D.Index) :=
          rfl
    simpa [map_smul, h_coe_smul] using congrArg Subtype.val ht
  have h_mem : ∑ k, x.intAction (star (p k).1) (x.torsionLift (μ k)) - x.torsionLift t ∈
      x.periodLattice := by
    have h_smul (c : 𝓞 E) (y : D.Index → E) :
        x.intAction c (x.periodPoint y) = x.periodPoint (c • y) := by
      simp [intAction, ← toRealVectors_smul]
    simp only [torsionLift, h_smul, ← map_sum]
    exact x.sub_mem_periodLattice_iff.mpr h_class
  obtain ⟨m, hm⟩ : ∃ m : ℤ, x.automorphyForm.riemannForm y
      (∑ k, x.intAction (star (p k).1) (x.torsionLift (μ k)) - x.torsionLift t) = m :=
    x.dualLattice_periodLattice.ge hy_mem _ h_mem
  -- Moving each coefficient across `x.automorphyForm` by adjunction turns `hp` into identities of
  -- sums.
  have h_norm (z : V) :
      ∑ k, x.automorphyForm u (x.intAction (star (p k).1) (x.intAction (p k).1 z)) = D.paddedNorm *
        x.automorphyForm u z := by
    simpa [map_sum, mul_sum, adjoint] using congrArg
      (fun c : 𝓞 E ↦ x.automorphyForm u (x.intAction c z)) hp_norm
  have h_orth : ∑ k, x.automorphyForm u (x.intAction (star (p k).1) (x.intAction (p k).2 w)) =
    0 := by
    simpa [map_sum, mul_sum, adjoint] using congrArg
      (fun c : 𝓞 E ↦ x.automorphyForm u (x.intAction c w)) hp_orth
  have h_chi : x.automorphyForm.riemannForm
    (x.intAction (D.rescaledBeta * ∑ k, star (p k).1 * (p k).1) u) u =
      x.automorphyForm.riemannForm (x.intAction (D.rescaledBeta * D.paddedNorm) u) u := by
        rw [hp_norm]
  -- `exp (π i r c) = exp (π i c) ^ r`, and `exp (2 π i m) = 1` drops out.
  have h_pow (c : ℂ) : cexp (Real.pi * I * (D.paddedNorm * c)) = cexp (Real.pi * I * c) ^
    D.paddedNorm := by
    simp [← exp_nat_mul, mul_left_comm]
  have h_int (c : ℂ) : cexp (2 * Real.pi * I * (c + m)) = cexp (2 * Real.pi * I * c) := by
    simp [mul_add, exp_add, mul_comm _ (m : ℂ)]
  -- By adjunction and `h_chi` the multipliers give `χ(u) ^ r`; by `hm` the phases give
  -- `e(⟨y, t⟩)`, since `e(m) = 1`.
  have h_multiplier : ∏ k, x.multiplier (x.intAction (p k).1 u) = x.multiplier u ^
    D.paddedNorm := by
    simp [← ofReal_inj, riemannForm_def, mul_sum, mul_left_comm, adjoint, div_eq_inv_mul,
      canonicalMultiplier] at h_chi ⊢
    simp only [← mul_sum] at h_chi
    simp only [← exp_sum, ← mul_sum, h_chi, h_pow]
  have h_phase : ∏ k, x.automorphyForm.riemannPhase (x.intAction (p k).1 y) (x.torsionLift (μ k)) =
      x.automorphyForm.riemannPhase y (x.torsionLift t) := by
    simp [← ofReal_inj, sub_eq_iff_eq_add', map_sub, riemannForm_def,
      torsionLift, periodPoint, adjoint, div_eq_inv_mul] at hm ⊢
    simp only [← mul_sum] at hm
    simp only [← exp_sum, ← mul_sum, hm, h_int]
  -- The twisted translation of the product is the product of the twisted translations: their
  -- exponents add up by `h_norm` and `h_orth`.
  have h_translate : (D.paddedNorm • x.automorphyForm).thetaShift u (x.thetaProduct p μ w) z =
      ∏ k, x.automorphyForm.thetaShift (x.intAction (p k).1 u) (x.thetaCoord (μ k))
        (x.intAction (p k).1 z + x.intAction (p k).2 w) := by
    simp [mul_left_comm, adjoint, div_eq_inv_mul, thetaShift_apply, exp_add,
      exp_neg, thetaProduct]
    simp only [prod_mul_distrib, prod_inv_distrib, ← exp_sum, ← mul_sum, h_orth, h_norm, exp_zero,
      inv_one, one_mul, mul_left_comm (2⁻¹ : ℂ), add_right_comm]
  rw [h_translate, prod_congr rfl fun k _ ↦ congrFun (h_shift k) _]
  simp only [Pi.smul_apply, smul_eq_mul, thetaProduct, ← h_multiplier, ← h_phase, prod_mul_distrib]

/-- Translation by a rational point shifts the indices of a theta product. Let `y` be a rational
vector whose class `[y]` lies in `D.dualTorsion` (`hy`), let `u = x.periodPoint y` be its image in
`V`, and let `p` be a Riemann tuple (`hp`). Then the twisted translation by `u` for `r B` sends
`x.thetaProduct p μ w` to `χ(u)^r e(⟨β u, ∑ ā_k μ_k⟩)` times the product for `μ + a [y]`, where `χ`
is `x.multiplier`, `β = D.rescaledBeta ∈ 𝓞 E`, for which `β u` lies in
`x.latticeOver D.dualTorsion`, `p k = (a_k, b_k)`, `r = D.paddedNorm` and
`B = x.automorphyForm`. -/
lemma thetaShift_periodPoint_thetaProduct {y : D.Index → E}
    (hy : frameTorsionClass g y ∈ D.dualTorsion)
    {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D) (μ : K → D.dualTorsion) (z : V) :
    (D.paddedNorm • x.automorphyForm).thetaShift (x.periodPoint y) (x.thetaProduct p μ w) z =
      x.multiplier (x.periodPoint y) ^ D.paddedNorm *
        x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.periodPoint y))
          (x.torsionLift ↑(∑ k : K, star (p k).1 • μ k)) *
        x.thetaProduct p (μ + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • ⟨frameTorsionClass g y, hy⟩) ∘ p) w z := by
  -- Apply `thetaShift_thetaProduct` with `t = ∑ ā_k μ_k` itself (so `ht` is `rfl`) and the point
  -- `β u`, which lies in the lattice over `D.dualTorsion`.
  refine x.thetaShift_thetaProduct hp (t := ∑ k, star (p k).1 • μ k) rfl
    (x.intAction_rescaledBeta_mem_latticeOver le_rfl (x.mem_latticeOver.mpr hy)) (fun k ↦ ?_) z
  -- `a_k u` is the image of the rational vector `a_k • y`, whose class is `a_k [y]`; the theta law
  -- (`PeriodMap.thetaShift_thetaCoord`) for it gives the factor for `k`.
  have h_act : x.intAction (p k).1 (x.periodPoint y) = x.periodPoint ((p k).1 • y) := by
    simp [intAction, ← toRealVectors_smul]
  have h_class : frameTorsionClass g ((p k).1 • y) =
      (((p k).1 • ⟨frameTorsionClass g y, hy⟩ : D.dualTorsion) : AdelicTorsion E D.Index) :=
        map_smul ..
  rw [h_act]
  simpa [intAction, smul_comm (cmEmbedding (p k).1.val), add_comm, periodPoint, bicharacter] using
    x.thetaShift_thetaCoord h_class (μ k)

/-- Riemann's theta relation in one variable. Here x is a theta torus on V for the PEL datum `D`.
T = `D.dualTorsion` is the finite group of classes pairing trivially with all integral vectors, r =
`D.paddedNorm` ≥ 3, and T[r] = `D.rTorsion` is the r-torsion of T. For a tuple p = (a, b) with
values in 𝓞 E, `x.thetaProduct p μ w` is P(μ; z) = ∏_k θ_{μ_k}(a_k z + b_k w), where θ_s =
`x.thetaCoord s`.

Let p = (a, b) satisfy ∑ ā a = r, ∑ ā b = 0 (`hp`) and ∑ ā μ = t. Let q = (a', b') satisfy the same
with μ' in place of μ, and write P' for the product attached to q. Then |T| P'(μ'; 0) P(μ; z) = √[T
: T[r]] ∑_{s ∈ T} P(μ − a s; 0) P'(μ' + a' s; z), with both products taken at the same point w. -/
lemma riemann_relation {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D)
    (ht : ∑ k : K, star (p k).1 • μ k = t) {q : K → 𝓞 E × 𝓞 E} (hq : IsRiemannTuple q D)
    (ht' : ∑ k : K, star (q k).1 • μ' k = t) [Fintype D.dualTorsion] (z : V) :
    Fintype.card D.dualTorsion * x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z =
      (D.rTorsion.relIndex D.dualTorsion).sqrt *
        ∑ s : D.dualTorsion,
          x.thetaProduct p (μ - (fun c : 𝓞 E × 𝓞 E ↦ c.1 • s) ∘ p) w 0 *
            x.thetaProduct q (μ' + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • s) ∘ q) w z := by
  -- Both products are theta functions of degree `r` for `x.latticeOver D.rTorsion`, whose dual
  -- lattice is `x.latticeOver D.dualTorsion`; apply Schur orthogonality over the lifts of
  -- `D.dualTorsion`.
  have hr : D.paddedNorm ≠ 0 := x.hasGoodReduction_one.one_lt.ne_bot
  have h_le : x.latticeOver D.rTorsion ≤ x.latticeOver D.lagrangian :=
    x.latticeOver_mono D.torsion_mem_lagrangian
  have h_dual : (D.paddedNorm • x.automorphyForm).dualLattice (L := x.latticeOver D.rTorsion) =
    x.latticeOver D.dualTorsion := by
    rw [← x.dualLattice_periodLattice]
    refine le_antisymm (dualLattice_nsmul_le hr fun _ ↦ (x.nsmul_mem_latticeOver hr).mp) ?_
    intro u hu l hl
    -- `r • l` lies in `x.periodLattice`, which pairs integrally with `u`.
    simpa using hu _ ((x.nsmul_mem_latticeOver hr).mpr hl)
  have h_discrete : DiscreteTopology (x.latticeOver D.rTorsion) :=
    x.discreteTopology_latticeOver_lagrangian.of_subset h_le
  have h_theta {p : K → 𝓞 E × 𝓞 E} {μ : K → D.dualTorsion} (hp : IsRiemannTuple p D)
      (hμ : ∑ k, star (p k).1 • μ k = t) :
      x.thetaProduct p μ w ∈
        (D.paddedNorm • x.automorphyForm).thetaSpace (L := x.latticeOver D.rTorsion) fun l ↦
          (x.multiplier ^ D.paddedNorm) l * x.automorphyForm.riemannPhase l (x.torsionLift t) := by
    have h_diff (s : D.dualTorsion) : Differentiable ℂ (x.thetaCoord s) :=
      (x.thetaCoord_mem_thetaSpace s).1
    refine ⟨by fun_prop [thetaProduct], fun l hl z ↦ ?_⟩
    -- Each factor is a theta function for `x.latticeOver D.lagrangian`, which contains the
    -- multiples of `l`.
    have h_mem (k : K) : x.intAction (p k).1 l ∈ x.latticeOver D.lagrangian := h_le <| by
      grind [=_ nsmul_mem_latticeOver, PEL.rTorsion, intAction_mem_periodLattice, =_ map_nsmul]
    simp only [Pi.pow_apply]
    rw [mul_right_comm,
      ← x.thetaShift_thetaProduct hp hμ (x.latticeOver_mono D.lagrangian_le_dualTorsion (h_le hl))
        fun k ↦
      thetaShift_of_mem (x.thetaCoord_mem_thetaSpace_lagrangian _) (h_mem k)]
    simp [field, thetaShift_apply, exp_add, exp_neg]
  let pt (s : D.dualTorsion) : (D.paddedNorm • x.automorphyForm).dualLattice
    (L := x.latticeOver D.rTorsion) :=
    ⟨x.torsionLift s, h_dual.ge (x.torsionLift_mem_latticeOver s)⟩
  -- Adding `u` permutes the lifts `pt s` modulo `x.latticeOver D.rTorsion`: `u` is the image of a
  -- rational vector `y`, and `s` goes to the class of `y` plus `s`.
  have h_perm (u : (D.paddedNorm • x.automorphyForm).dualLattice (L := x.latticeOver D.rTorsion)) :
      ∃ e : D.dualTorsion ≃ D.dualTorsion, ∀ s : D.dualTorsion,
        ↑(u + pt s - pt (e s)) ∈ x.latticeOver D.rTorsion := by
    obtain ⟨y, hy, hyu⟩ : ∃ y : D.Index → E,
      frameTorsionClass g y ∈ D.dualTorsion ∧ x.periodPoint y = u :=
      h_dual.le u.property
    use .addLeft ⟨_, hy⟩
    have h_class_zero (a : AdelicTorsion E D.Index) :
        frameTorsionClass g (y + ratLift g a - ratLift g (frameTorsionClass g y + a)) = 0 := by simp
    simp [pt, ← hyu, ← map_add, ← map_sub, torsionLift, h_class_zero]
  -- The Appell–Humbert datum of degree `r` for which both products are theta functions.
  have h_datum : IsAppellHumbert (L := x.latticeOver D.rTorsion) (D.paddedNorm • x.automorphyForm)
      fun l ↦ (x.multiplier ^ D.paddedNorm) l * x.automorphyForm.riemannPhase l (x.torsionLift t) :=
    ((x.isAppellHumbert_of_le h_le).nsmul _).mul_riemannPhase (x.torsionLift t) x.automorphyForm
  -- Schur orthogonality for the translates by the lifts `pt s`.
  have h_appell :
      ((D.rTorsion.relIndex D.dualTorsion).sqrt : ℂ) *
          ∑ s : D.dualTorsion, (D.paddedNorm • x.automorphyForm).thetaShift (-(pt s : V))
            (x.thetaProduct p μ w) 0 *
            (D.paddedNorm • x.automorphyForm).thetaShift (pt s) (x.thetaProduct q μ' w) z =
        Fintype.card D.dualTorsion * x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z := by
    rw [← x.relIndex_latticeOver, ← h_dual]
    exact h_datum.sum_shift_mul_shift (hp := x.isPosRiemann.nsmul hr) D.dualTorsion pt h_perm
      ⟨_, h_theta hq ht'⟩ ⟨_, h_theta hp ht⟩ 0 z
  rw [← h_appell]
  congr with s
  -- The factors for `-s` and `s` cancel: the multiplier at the lift of `s`, written as an
  -- exponential, has `2 r`-th power `1` (`PeriodMap.riemannPhase_rescaledBeta_eq`).
  have h_phase : x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.torsionLift s))
        (x.periodPoint (ratLift g s)) =
      x.automorphyForm.riemannPhase (x.periodPoint (ratLift g s))
        ((Nat.card D.dualTorsion / 2) • x.torsionLift s) :=
    x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem_latticeOver s)
      (x.torsionLift_mem_latticeOver s) rfl
  have h_multiplier_sq :
      (cexp (Real.pi * I *
        (x.automorphyForm.riemannForm (x.intAction D.rescaledBeta
          (x.realEquiv (toRealVectors (ratLift g s))))
          (x.realEquiv (toRealVectors (ratLift g s))) : ℂ)) ^ D.paddedNorm) ^ 2 = 1 := by
    simpa [two_mul, add_mul, sq, torsionLift, periodPoint, canonicalMultiplier, exp_add, mul_pow]
      using congrArg (fun c : ℂ ↦ c ^ D.paddedNorm) h_phase
  have h_neg : -x.torsionLift s = x.periodPoint (-ratLift g s) := by simp [torsionLift, periodPoint]
  have h_neg_s : (⟨-s.val, neg_mem s.property⟩ : D.dualTorsion) = -s := rfl
  change (D.paddedNorm • x.automorphyForm).thetaShift (-x.torsionLift s) (x.thetaProduct p μ w) 0 *
      (D.paddedNorm • x.automorphyForm).thetaShift (x.torsionLift s) (x.thetaProduct q μ' w) z = _
  -- Translation by `∓` the lift of `s` shifts the indices (`thetaShift_periodPoint_thetaProduct`).
  rw [h_neg, torsionLift, x.thetaShift_periodPoint_thetaProduct (y := -ratLift g s) (by simp) hp,
    x.thetaShift_periodPoint_thetaProduct (y := ratLift g s) (by simp) hq]
  simp [ht, ht', field, sub_eq_add_neg, ← smul_neg, periodPoint, canonicalMultiplier, exp_neg,
    thetaProduct, h_neg_s, h_multiplier_sq]

/-- Let `θ_o(0)` have the largest valuation among the theta constants `θ_t(0)` (`ho`), and let that
valuation be at most those of `θ_{s-u}(0)` and `θ_{-u}(0)` (`h_best`). Then each of `θ_u(0)`,
`θ_{-u}(0)`, `θ_{s-u}(0)` has the largest valuation. -/
private lemma valuation_thetaCoord_le_of_le_inf {s u o : D.dualTorsion}
    (ho : ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord o 0))
    (h_best : v (x.thetaCoord o 0) ≤ v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)) :
    ∀ i ∈ [u, -u, s - u], ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
  -- The symmetry `PeriodMap.exists_thetaCoord_sign_smul`, used twice at `0`, carries the bound
  -- from `-u` to `u`.
  obtain ⟨η, hη⟩ := x.exists_thetaCoord_sign_smul (-1)
  have h_symm (t : D.dualTorsion) : x.thetaCoord t 0 = η * x.thetaCoord (-t) 0 := by
    simpa using hη 0 t
  -- For `-u` and `s - u` the bound is `h_best` with `ho`.
  have h_rest : ∀ i ∈ [-u, s - u], ∀ t : D.dualTorsion,
    v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
    grind
  refine List.forall_mem_cons.mpr ⟨fun t ↦ ?_, h_rest⟩
  calc v (x.thetaCoord t 0) = v η * v (x.thetaCoord (-t) 0) := by rw [h_symm, map_mul]
    _ ≤ v η * v (x.thetaCoord (-u) 0) := by grw [ho (-t), h_best.trans inf_le_right]
    _ = v (x.thetaCoord u 0) := by rw [h_symm u, map_mul]

/-- The bound on the values of the size function in the proof of
`exists_forall_valuation_thetaCoord_zero_le`. Let `r = D.paddedNorm = k + 3` and `v |T| = 1` (`hv`),
let `θ_o(0) ≠ 0` have the largest valuation `top` among the theta constants (`ho`), and let `u`
maximise `min (v θ_{s-t}(0)) (v θ_{-t}(0))` over `t`, with maximum `best` (`hu`). If every
`v θ_t(z)` is at most `v (exp (B(z, z) / 2)) ρ` (`h_le`), `ρ` the norm of `θ_0`, then at each
torsion point `z` the product of the sizes (`New.ThetaTori.LatticeForm.sizeAt`) of `θ_s`,
`θ_{r o - s}` and `θ_0 ^ (k + 1)`, times `top`, is at most `best ρ ^ r`. The proof applies Riemann's
relation and the ultrametric inequality. Here `T = D.dualTorsion` and `B = x.automorphyForm`. -/
private lemma mul_sizeAt_le_inf_mul_thetaNorm_pow [Fintype D.dualTorsion] {s o u : D.dualTorsion}
    {k : ℕ} (hr_eq : D.paddedNorm = 2 + k + 1) (hv : v (Fintype.card D.dualTorsion) = 1)
    (ho : ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord o 0))
    (hu : ∀ t : D.dualTorsion, v (x.thetaCoord (s - t) 0) ⊓ v (x.thetaCoord (-t) 0) ≤
      v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0))
    (h_top : x.thetaCoord o 0 ≠ 0)
    (h_le : ∀ (t : D.dualTorsion) (z : torsionPoints x.periodLattice),
      v (x.thetaCoord t z) ≤ v (exp (x.automorphyForm z z / 2)) * x.automorphyForm.thetaNorm v
        (x.thetaCoord 0))
    (z : torsionPoints x.periodLattice) :
    v (x.thetaCoord o 0) *
        (x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
          (x.thetaCoord (D.paddedNorm • o - s)) *
          ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))) z ≤
      (v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)) *
        x.automorphyForm.thetaNorm v (x.thetaCoord 0) ^ D.paddedNorm := by
  set top : ℝ≥0 := v (x.thetaCoord o 0)
  set best : ℝ≥0 := v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)
  set ρ : ℝ≥0 := x.automorphyForm.thetaNorm v (x.thetaCoord 0)
  set φ := x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) *
    ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))
  let κ : Type := Option (Fin 2 ⊕ Fin k)
  let μ : κ → D.dualTorsion := fun i ↦ i.elim (D.paddedNorm • o - s) (Sum.elim ![s, 0] 0)
  let oneZero : κ → 𝓞 E × 𝓞 E := const κ (1, 0)
  have h_one : IsRiemannTuple oneZero D := by simp [IsRiemannTuple, oneZero, κ, hr_eq]
  -- `|T| θ_o(0) ^ r P(μ; z) = √index ∑ t, P(μ - t; 0) θ_{o + t}(z) ^ r`, where `P(μ; ·)` is the
  -- product of the `θ_{μ i}`.
  have h_sum : ∑ i : κ, star (oneZero i).1 • μ i = ∑ i : κ, star (oneZero i).1 • const κ o i := by
    simp [oneZero, κ, μ, hr_eq]
  let term (t : D.dualTorsion) : ℂ :=
    x.thetaProduct oneZero (μ - (fun c : 𝓞 E × 𝓞 E ↦ c.1 • t) ∘ oneZero) 0 0 *
      x.thetaProduct oneZero (const κ o + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • t) ∘ oneZero) 0 z
  have h_rel :
      (Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0 *
          x.thetaProduct oneZero μ 0 z = (D.rTorsion.relIndex D.dualTorsion).sqrt * ∑ t :
            D.dualTorsion, term t :=
    x.riemann_relation (w := 0) h_one h_sum h_one rfl z
  have h_bound :
      v (card D.dualTorsion * x.thetaProduct oneZero (const κ o) 0 0 * x.thetaProduct oneZero μ 0 z)
        ≤
        best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^ D.paddedNorm := by
    -- Bound each term on the right of `h_rel` (ultrametric inequality): one constant is at most
    -- `best`, the others at most `top`. `v.leSubmodule c` is the set of `y` with `v y ≤ c`.
    rw [h_rel]
    suffices h_terms : ∑ t : D.dualTorsion, term t ∈
          v.leSubmodule (best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^
            D.paddedNorm) from
      (v.leSubmodule _).smul_mem (Nat.cast (D.rTorsion.relIndex D.dualTorsion).sqrt) h_terms
    refine sum_mem fun t _ ↦ ?_
    have h_pair : v (x.thetaCoord (s - t) 0) * v (x.thetaCoord (-t) 0) ≤ best * top := by
      grw [← min_mul_max, hu t, max_le (ho (s - t)) (ho (-t))]
    calc v _ = v (x.thetaCoord (D.paddedNorm • o - s - t) 0) *
          (v (x.thetaCoord (s - t) 0) * v (x.thetaCoord (-t) 0) * v (x.thetaCoord (-t) 0) ^ k) *
          v (x.thetaCoord (o + t) z) ^ D.paddedNorm := by
            simp [term, oneZero, κ, μ, hr_eq, thetaProduct]
      _ ≤ top * (best * top * top ^ k) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^
        D.paddedNorm := by
        grw [h_pair, ho (D.paddedNorm • o - s - t), ho (-t), h_le]
      _ = _ := by ring
  -- Compare `h_bound` with the goal: with `e = v (exp (B(z, z) / 2))`, the product for `μ` has
  -- valuation `φ z * e ^ r`, and the constant factor has valuation `top ^ r`.
  have h_φ : φ z * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm = v
    (x.thetaProduct oneZero μ 0 z) := by
    simp only [φ, Pi.mul_apply, sizeAt_pow, Pi.pow_apply]
    simp [sizeAt, thetaProduct, oneZero, κ, μ, hr_eq, thetaShift_apply, exp_neg, field, pow_add,
      mul_pow]
  have h_const :
      v ((Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0) = top ^
        D.paddedNorm := by
    simp [thetaProduct, oneZero, κ, hv, hr_eq, top]
  have h_e_pos : 0 < v (exp (x.automorphyForm z z / 2)) := by simp [Valuation.pos_iff, exp_ne_zero]
  have h_top_pos : 0 < top := by simpa [top, Valuation.pos_iff] using h_top
  refine le_of_mul_le_mul_left ?_ (mul_pos (pow_pos h_top_pos (k + 2))
    (pow_pos h_e_pos D.paddedNorm))
  calc top ^ (k + 2) * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm * (top * φ z)
      = v ((Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0 *
          x.thetaProduct oneZero μ 0 z) := by
        rw [map_mul, h_const, ← h_φ, hr_eq]
        ring
    _ ≤ best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^ D.paddedNorm := h_bound
    _ = top ^ (k + 2) * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm *
      (best * ρ ^ D.paddedNorm) := by ring

/-- Under good reduction at `v` (`h_good`, see `New.ThetaTori.HasGoodReduction`) and
`v |T| = 1` (`hv`), for every `s` in `T = D.dualTorsion` there is `u` such that each of the theta
constants `θ_u(0)`, `θ_{-u}(0)`, `θ_{s-u}(0)` has the largest valuation among all `θ_t(0)`. So `s`
is both a sum `u + (s - u)` and a difference `(s - u) - (-u)` of such indices. -/
lemma exists_forall_valuation_thetaCoord_zero_le (h_good : HasGoodReduction x.automorphyForm
  x.multiplier v D.paddedNorm) (hv : v (Nat.card D.dualTorsion) = 1)
    (s : D.dualTorsion) :
    ∃ u : D.dualTorsion, ∀ i ∈ [u, -u, s - u], ∀ t : D.dualTorsion,
      v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
  -- Let `top` be the largest of the `v (θ_t 0)`, taken at `o`, and `best` the largest of the minima
  -- of `v (θ_{s - t} 0)` and `v (θ_{-t} 0)`, taken at `u`. Riemann's relation for
  -- `θ_{r o - s} θ_s θ_0 ^ (r - 2)` and `θ_o ^ r`, with the multiplicative norm, gives
  -- `top ≤ best`. Here `r = D.paddedNorm`.
  cases nonempty_fintype D.dualTorsion
  obtain ⟨k, hr_eq⟩ : ∃ k : ℕ, D.paddedNorm = 2 + k + 1 :=
    Nat.exists_eq_add_of_lt D.three_le_paddedNorm
  obtain ⟨o, ho⟩ := exists_max fun t : D.dualTorsion ↦ v (x.thetaCoord t 0)
  obtain ⟨u, hu⟩ := exists_max fun t : D.dualTorsion ↦
    v (x.thetaCoord (s - t) 0) ⊓ v (x.thetaCoord (-t) 0)
  set top : ℝ≥0 := v (x.thetaCoord o 0)
  set best : ℝ≥0 := v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)
  suffices h_best : top ≤ best from ⟨u, x.valuation_thetaCoord_le_of_le_inf ho h_best⟩
  -- All `x.thetaCoord t` have the same norm `ρ > 0`, and they do not all vanish at `0`.
  set ρ : ℝ≥0 := x.automorphyForm.thetaNorm v (x.thetaCoord 0)
  have hρ : 0 < ρ := h_good.thetaNorm_pos (x.thetaCoord_mem_thetaSpace 0) (x.thetaCoord_ne_zero 0)
  have h_top : x.thetaCoord o 0 ≠ 0 := fun h_zero ↦ x.thetaCoord_vector_ne_zero 0 <|
    funext fun t ↦ by simpa [top, h_zero] using ho t
  have h_size_mem (t : D.dualTorsion) : x.automorphyForm.sizeAt v (x.thetaCoord t) ∈
    x.automorphyForm.sizes v :=
    .of_mem_thetaSpace h_good.toIsAmpleType (x.thetaCoord_mem_thetaSpace t)
  have h_le (t : D.dualTorsion) (z : torsionPoints x.periodLattice) :
      v (x.thetaCoord t z) ≤ v (exp (x.automorphyForm z z / 2)) * ρ := by
    simpa [sizeAt, field, thetaNorm_thetaCoord, thetaShift_apply, exp_neg, Valuation.pos_iff] using
      le_iSup_of_mem_sizes (h_size_mem t) z
  -- The norm is multiplicative, so the size `φ` of the product has norm `ρ ^ r`.
  set φ := x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) *
    ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))
  have h_sz_mul : x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) ∈
      (x.automorphyForm + x.automorphyForm).sizes v := by
    simpa [Pi.mul_def] using mul_shift_mem_sizes (h_size_mem s) (h_size_mem (D.paddedNorm • o - s))
      0
  have h_norm : iSup φ = ρ ^ D.paddedNorm := by
    rw [h_good.hasMultiplicativeNorm h_sz_mul
        (.of_mem_thetaSpace (h_good.nsmul k.succ_ne_zero) (pow (x.thetaCoord_mem_thetaSpace 0) _)),
      h_good.hasMultiplicativeNorm (h_size_mem _) (h_size_mem _)]
    grind [thetaNorm_pow, thetaNorm_thetaCoord]
  -- It suffices to bound the values of `φ`: take the supremum and cancel `ρ ^ r`.
  suffices h_value : ∀ z : torsionPoints x.periodLattice, top * φ z ≤ best * ρ ^ D.paddedNorm by
    have h_sup : top * ρ ^ D.paddedNorm ≤ best * ρ ^ D.paddedNorm := by
      simpa [h_norm] using mul_iSup_le h_value
    exact le_of_mul_le_mul_right h_sup (pow_pos hρ D.paddedNorm)
  exact x.mul_sizeAt_le_inf_mul_thetaNorm_pow hr_eq (by simpa using hv) ho hu h_top h_le

/-- Along a surjective ring map `φ : A →+* B`, every form of degree `d` over `B` is the image of a
form of degree `d` over `A`: mapping coefficients by `φ` is surjective on homogeneous
polynomials of degree `d`. -/
lemma surjective_map_homogeneous {σ A B : Type} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : Surjective φ) (d : ℕ) :
    Surjective fun f : homogeneousSubmodule σ A d ↦
      (⟨f.val.map φ, f.property.map φ⟩ : homogeneousSubmodule σ B d) := by
  rintro ⟨g, hg⟩
  -- Lift `g` coefficient by coefficient along a right inverse of `φ`.
  let f : MvPolynomial σ A := ∑ m ∈ g.support, monomial m (surjInv hφ (g.coeff m))
  have hf_hom : f ∈ homogeneousSubmodule σ A d :=
    sum_mem fun m hm ↦ isHomogeneous_monomial _ (hg.degree_eq_sum_deg_support hm).symm
  exact ⟨⟨f, hf_hom⟩, Subtype.ext (by simp [f, surjInv_eq])⟩

/-- A form `f` of degree `r ^ j` in the theta coordinates is small at the chart `c` if the theta
function `f(θ)` has norm (`New.ThetaTori.LatticeForm.thetaNorm` at `v` for `r ^ j • B`) below
`‖θ_c‖ ^ (r ^ j)`, the norm of `θ_c ^ (r ^ j)`. Here `r = D.paddedNorm` and
`B = x.automorphyForm`. -/
private def IsSmallForm (c : D.dualTorsion) (j : ℕ)
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) : Prop :=
  (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v
    (aeval x.thetaCoord (f : MvPolynomial D.dualTorsion v.valuationSubring)) <
    x.automorphyForm.thetaNorm v (x.thetaCoord c) ^ D.paddedNorm ^ j

/-- Under good reduction, the forms of degree `r ^ j` in the theta coordinates with integral
coefficients give exactly the norm ball of `θ_c ^ (r ^ j)`: the theta functions of `r ^ j • B` with
norm at most that of `θ_c ^ (r ^ j)` (`h_good.pow j` is good reduction for `r ^ j • B`). Here
`r = D.paddedNorm` and `B = x.automorphyForm`. -/
private lemma range_aeval_thetaCoord_eq_normBall
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    (c : D.dualTorsion) (j : ℕ) :
    ((aeval x.thetaCoord).toLinearMap.domRestrict
      (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))).range =
      (h_good.pow j).normBall (x.thetaCoord c ^ D.paddedNorm ^ j) := by
  rw [LinearMap.range_domRestrict, map_homogeneousSubmodule_eq_formSpan,
    x.formSpan_eq_normBall v h_good]

/-- Smallness is read off from reductions at points that represent the dual lattice. Let `x` have
good reduction at `v` (`h_good`) and let `φ` map the valuation ring of `v` onto a field `k`. Let the
points `a b` represent the dual lattice of `r ^ j • B` modulo `x.periodLattice` (`ha`), and let
`p b` be integral coordinates of the theta vector at `a b` (`hp`). Then a form `f` of degree
`r ^ j` is small at `c` iff its reduction by `φ` vanishes at every point `φ ∘ p b`. Here
`r = D.paddedNorm` and `B = x.automorphyForm`. -/
private lemma isSmallForm_iff_forall_eval_map_eq_zero [Field k] {φ : v.valuationSubring →+* k}
    (hφ : Surjective φ) (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    (c : D.dualTorsion) (j : ℕ) {I : Type} {a : I → V} {p : I → D.dualTorsion → v.valuationSubring}
    (ha : ∀ u : (D.paddedNorm ^ j • x.automorphyForm).dualLattice, ∃ b : I,
      a b - u ∈ x.periodLattice)
    (hp : ∀ b : I, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s (a b)) (p b))
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
    x.IsSmallForm c j f ↔ ∀ b : I, (f.val.map φ).eval (φ ∘ p b) = 0 := by
  let ev : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)
    →ₗ[v.valuationSubring] V → ℂ :=
    (aeval x.thetaCoord).toLinearMap.domRestrict
      (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))
  have h_max (y : v.valuationSubring) : φ y = 0 ↔ v y < 1 := by
    simp [← v.mem_maximalIdeal_iff, ← IsLocalRing.ker_eq_maximalIdeal φ hφ]
  -- By homogeneity the values of the forms at `p b` are integral coordinates of their values at
  -- `a b`; the power of a unit coordinate is a unit.
  have h_aff (b : I) : IsIntegralCoords (fun g ↦ ev g (a b)) fun g ↦ g.val.eval (p b) := by
    obtain ⟨s, hs_eq, i, hi_unit⟩ : ∃ s : ℂ,
      (∀ t : D.dualTorsion, (p b t : ℂ) = x.thetaCoord t (a b) / s) ∧
        ∃ i : D.dualTorsion, v (p b i) = 1 := hp b
    refine ⟨s ^ D.paddedNorm ^ j, fun g ↦ ?_, ⟨_, isHomogeneous_X_pow i _⟩, by simp [hi_unit]⟩
    simpa [ev, eval_eq, aeval_def, eval₂_eq, hs_eq, div_eq_inv_mul] using
      eval₂_mul_of_isHomogeneous g.property (algebraMap ..) s⁻¹ _
  have h_ball : ev.range = (h_good.pow j).normBall (x.thetaCoord c ^ D.paddedNorm ^ j) :=
    x.range_aeval_thetaCoord_eq_normBall h_good c j
  show (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (ev f) < x.automorphyForm.thetaNorm v
    (x.thetaCoord c) ^ D.paddedNorm ^ j ↔ _
  simpa [thetaNorm_pow, ← h_max, map_eval] using
    (h_good.pow j).thetaNorm_lt_iff_coords (pow (x.thetaCoord_mem_thetaSpace c) _)
      (pow_ne_zero _ (x.thetaCoord_ne_zero c)) h_ball ha h_aff f

/-- Smallness is read off at the points of the chart `c`. Under good reduction (`h_good`), with
`φ` onto a field and `q z` integral coordinates of the theta vector at every `z ∈ V` (`hq`), a
form `f` of degree `r ^ j` is small at `c` iff its reduction vanishes at each point `φ ∘ q z`
whose coordinate `c` is nonzero. Here `r = D.paddedNorm`. -/
private lemma isSmallForm_iff_forall_eval_map_eq_zero_of_ne_zero [Field k]
    {φ : v.valuationSubring →+* k} (hφ : Surjective φ)
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    {q : V → D.dualTorsion → v.valuationSubring}
    (hq : ∀ z : V, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s z) (q z))
      (c : D.dualTorsion) (j : ℕ)
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
    x.IsSmallForm c j f ↔ ∀ z : V, φ (q z c) ≠ 0 → (f.val.map φ).eval (φ ∘ q z) = 0 := by
  -- Multiplying `f` by `X c ^ e` to reach degree `r ^ (j + 1)` multiplies norm and radius by the
  -- same factor. In that degree all points of `V` may be used, and `X c ^ e` vanishes exactly
  -- where the coordinate `c` does.
  obtain ⟨e, he_pos, h_deg⟩ : ∃ e > 0, D.paddedNorm ^ (j + 1) = D.paddedNorm ^ j + e :=
    lt_iff_exists_add.mp (Nat.pow_lt_pow_succ (n := j) h_good.one_lt)
  have hρ : 0 < x.automorphyForm.thetaNorm v (x.thetaCoord c) :=
    h_good.thetaNorm_pos (x.thetaCoord_mem_thetaSpace c) (x.thetaCoord_ne_zero c)
  have h_hom : IsHomogeneous (f.val * X c ^ e) (D.paddedNorm ^ (j + 1)) := by
    simpa [h_deg] using f.property.mul (isHomogeneous_X_pow c e)
  let f' : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ (j + 1)) :=
    ⟨f.val * X c ^ e, h_hom⟩
  have h_mul : (D.paddedNorm ^ (j + 1) • x.automorphyForm).thetaNorm v
    (aeval x.thetaCoord (f.val * X c ^ e)) =
      (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (aeval x.thetaCoord f.val) *
        x.automorphyForm.thetaNorm v (x.thetaCoord c) ^ e := by
    have h_mem_ball : aeval x.thetaCoord f.val ∈
        (h_good.pow j).normBall (x.thetaCoord c ^ D.paddedNorm ^ j) :=
      (x.range_aeval_thetaCoord_eq_normBall h_good c j).le ⟨f, rfl⟩
    rw [map_mul, map_pow, aeval_X, h_deg, add_smul, ← thetaNorm_pow, LatticeForm.thetaNorm,
      sizeAt_mul]
    exact h_good.hasMultiplicativeNorm
      (.of_mem_thetaSpace (h_good.pow j).toIsAmpleType (Submodule.mem_inf.mp h_mem_ball).left)
      (.of_mem_thetaSpace (h_good.nsmul he_pos.ne') (pow (x.thetaCoord_mem_thetaSpace c) e))
  have h_small : x.IsSmallForm c (j + 1) f' ↔ x.IsSmallForm c j f := by
    simp_rw [IsSmallForm, f', h_mul, h_deg, pow_add, mul_lt_mul_iff_left₀ (pow_pos hρ e)]
  rw [← h_small, x.isSmallForm_iff_forall_eval_map_eq_zero hφ h_good c (j + 1)
    (fun u ↦ ⟨(u : V), by simp⟩) hq f']
  simp [f', he_pos.ne', or_iff_not_imp_right]

/-- Under good reduction at `v` (`h_good`), with `φ` onto a field `k`, `q z` integral coordinates of
the theta vector `(θ_s(z))_s` at every `z ∈ V` and `p l` those at the lift of each level point `l`:
if each `N l` has the coordinates `φ ∘ p l` at `t`, then `N` cuts out at `t` the reduced vectors
`φ ∘ q z` (`New.Variety.ThetaNull.IsCutOutAt`). That is: in all charts of the `N l` at `t` and each
chart `c`, the ideal of those vectors with `c`-coordinate ≠ 0, scaled to 1, satisfies
`IsCutOut D.paddedNorm D.exponentBound` with ranks `thetaRanks D.dualTorsion D.paddedNorm` (the
dimensions of the theta spaces of `r ^ j • x.automorphyForm`; for `j ≤ D.exponentBound` the level
points `D.levelTorsion` represent its dual lattice mod `x.periodLattice`) for the affine coordinates
of the `N l` at `t`. Here `r = D.paddedNorm`. -/
lemma isCutOutAt_reduction [Field k] {φ : v.valuationSubring →+* k} (hφ : Surjective φ)
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    {q : V → D.dualTorsion → v.valuationSubring}
      {p : D.levelTorsion → D.dualTorsion → v.valuationSubring}
    (hq_coords : ∀ z : V, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s z) (q z))
    (hp_coords : ∀ l : D.levelTorsion,
      IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s (x.torsionLift l)) (p l))
    {S : AlgebraicGeometry.Scheme} {t : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ S}
    {N : D.levelTorsion → LineBundle S D.dualTorsion}
    (hN_coords : ∀ l : ↥D.levelTorsion, (N l).IsHomogeneousCoords t fun s : D.dualTorsion ↦
      φ (p l s)) :
    IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) N t
      (Set.range fun z : V ↦ φ ∘ q z) := by
  -- In the chart `c` the forms of degree `r ^ j` vanishing at the reduced points are the small
  -- ones, so the ranks are those of the reduced norm balls and may be read at the level points.
  intro chart h_chart c
  have h_dual (j : ℕ) :
      (D.paddedNorm ^ j • x.automorphyForm).dualLattice = x.latticeOver
        (D.dualTorsion.comap (nsmulAddMonoidHom (D.paddedNorm ^ j))) := by
    ext u
    rw [mem_dualLattice_nsmul, x.dualLattice_periodLattice,
      x.nsmul_mem_latticeOver (pow_ne_zero j h_good.one_lt.ne_bot)]
  -- `J` is the ideal of the reduced points in the chart `c`.
  let J : Ideal (MvPolynomial D.dualTorsion k) :=
    ⨅ pt ∈ {pt ∈ Set.range (fun z : V ↦ φ ∘ q z) | pt c ≠ 0},
      RingHom.ker (MvPolynomial.eval fun s : D.dualTorsion ↦ pt s / pt c)
  have h_ideal (j : ℕ) (f : homogeneousSubmodule D.dualTorsion v.valuationSubring
    (D.paddedNorm ^ j)) :
      f.val.map φ ∈ J ↔ x.IsSmallForm c j f := by
    simp +contextual [J, x.isSmallForm_iff_forall_eval_map_eq_zero_of_ne_zero hφ h_good hq_coords,
      eval₂_mul_of_isHomogeneous f.property, div_eq_inv_mul]
  have h_lift (d : ℕ) : Surjective fun f : homogeneousSubmodule D.dualTorsion v.valuationSubring d ↦
      (⟨f.val.map φ, f.property.map φ⟩ : homogeneousSubmodule D.dualTorsion k d) :=
    surjective_map_homogeneous hφ d
  refine ⟨by simp +contextual, fun j ↦ ?_, fun j hj ↦ ?_⟩
  · -- The rank is the dimension of the theta space, whose square is an index of lattices.
    let red : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j) →ₛₗ[φ]
      MvPolynomial D.dualTorsion k ⧸ J :=
      { toFun f := Ideal.Quotient.mk J (f.val.map φ)
        map_add' := by simp
        map_smul' c f := by
          have h_alg :
              algebraMap k (MvPolynomial D.dualTorsion k ⧸ J) (φ c) = Ideal.Quotient.mk J
                (C (φ c)) := rfl
          simp [Algebra.smul_def, h_alg] }
    have h_range : imageMod J (homogeneousSubmodule D.dualTorsion k (D.paddedNorm ^ j)) = span k
      (Set.range red) := by
      rw [← (imageMod ..).span_eq, map_coe, Set.image_eq_range, ← (h_lift _).range_comp]
      rfl
    have h_zero (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
        red f = 0 ↔ (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (aeval x.thetaCoord f.val) <
          (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v
            (x.thetaCoord c ^ D.paddedNorm ^ j) := by
      rw [thetaNorm_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.trans (h_ideal j f)

    -- The rank is the dimension of the theta space of degree `r ^ j` ...
    have h_ball : ((aeval x.thetaCoord).toLinearMap.domRestrict
          (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))).range =
        (h_good.pow j).normBall (x.thetaCoord c ^ D.paddedNorm ^ j) :=
      x.range_aeval_thetaCoord_eq_normBall h_good c j
    change finrank k (imageMod J (homogeneousSubmodule D.dualTorsion k (D.paddedNorm ^ j))) =
      thetaRanks D.dualTorsion D.paddedNorm j
    rw [h_range, (h_good.pow j).finrank_reduction_eq (pow (x.thetaCoord_mem_thetaSpace c) _)
      (pow_ne_zero _ (x.thetaCoord_ne_zero c)) h_ball hφ h_zero]
    -- ... whose square is the index of `x.periodLattice` in the dual lattice.
    rw [← Nat.sqrt_eq' (finrank ..),
      (h_good.pow j).finrank_thetaSpace_sq (hp := (h_good.pow j).isPosRiemann), h_dual,
      x.relIndex_latticeOver]
    simp [thetaRanks]
  · -- For `j ≤ D.exponentBound` the level points represent the dual lattice in degree `r ^ j`
    -- modulo `x.periodLattice`: its classes are killed by the level (`D.mem_torsionBy_level`).
    have h_repr : ∀ u : (D.paddedNorm ^ j • x.automorphyForm).dualLattice, ∃ l : D.levelTorsion,
        x.torsionLift l - u ∈ x.periodLattice := by
      rw [h_dual]
      rintro ⟨_, y, hy_class, rfl⟩
      use ⟨_, D.mem_torsionBy_level _ hj _ hy_class⟩
      simp [torsionLift, sub_mem_periodLattice_iff]
    intro f₀ hf₀
    -- `f₀` is the reduction of a form `f` over the valuation ring.
    obtain ⟨f, hf⟩ := h_lift (D.paddedNorm ^ j) ⟨f₀, hf₀⟩
    obtain rfl : f.val.map φ = f₀ := congrArg Subtype.val hf
    refine (h_ideal j f).trans
      ((x.isSmallForm_iff_forall_eval_map_eq_zero hφ h_good c j h_repr hp_coords f).trans ?_)
    -- The coordinates at `t` are those of `φ ∘ p b` divided by a nonzero one, the coordinate of the
    -- chart `chart b`.
    have h_unit (b : D.levelTorsion) : φ (p b (chart b)) ≠ 0 :=
      ((hN_coords b (chart b)).left.mp (h_chart b)).ne_zero
    simp [hN_coords _ _, h_unit, eval₂_mul_of_isHomogeneous f.property, comp_def, mul_comm (φ _)]

/-- The family of coefficient pairs in `𝓞 E` consisting of `(1, 0)` twice (on the first copy of
`Bool`), `(c, 1)` and `(1, −c̄)` (at `true` and `false` of the second copy), and `(a l, 0)` for
every `l : K`. -/
def _root_.New.paddingTuple (c : 𝓞 E) : Bool ⊕ Bool ⊕ K → 𝓞 E × 𝓞 E :=
  Sum.elim (fun _ : Bool ↦ (1, 0)) (Sum.elim (fun b ↦ cond b (c, 1) (1, -star c)) fun l ↦ (a l, 0))

end New.ThetaTori.ThetaTorus

end
