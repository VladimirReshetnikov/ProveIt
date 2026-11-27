import Lib.Shimura.ThetaModuli.PELThetaTori
import Lib.Shimura.Transfer.MarkedPairs

/-!
# Period signatures, analytic families of theta tori and the ball chart of moduli points

Φ v denotes the embedding E → ℂ that the CM type chooses at the infinite place v, and v₀ is the base
infinite place fixed by `New.CMBase`. Theta tori that vary analytically with a parameter b in a
domain of ℂⁿ⁻¹, all uniformised by one fixed space V, form analytic families. Near each b₀, their
theta coordinates become analytic after a common factor c(b) ≠ 0. For a fixed frame, the positive
lines form a ball, and the moduli points with this frame are the points of a single analytic family
over that ball.

## Main definitions and results

* `New.ThetaTori.PeriodMap.isSignedFrameFor`: the sign condition on the matrix of a polarised period
  map.
* `New.Variety.AnalyticFamily`: a family of theta tori, with periods Q_b analytic in b and with
  B(Q_b ·, ·) independent of b.
* `New.Variety.AnalyticFamily.exists_analytic_thetaCoord`: near b₀, after a common factor c(b) ≠ 0,
  the theta coordinates are analytic in (b, z).
* `New.Variety.positiveBall`, `New.Variety.exists_ball_chart`: the positive lines, in coordinates
  ℂ × ℂ^(n−1); the set is star-convex, hence connected.
* `New.Variety.ballPeriod`: an explicit period map (E ⊗ ℝ)ⁿ → `New.Variety.BallFibre`, affine in the
  point.
* `New.Variety.exists_analyticFamily_positiveBall`: the ball carries an analytic family
  `New.Variety.AnalyticFamily` with these periods and the reflections `New.Variety.formReflection`.
* `New.Variety.IsBallFamily`, `New.Variety.exists_isBallFamily`: the points with the frame of a
  given point o are the points `New.Variety.AnalyticFamily.ballPoint` of one analytic family. An
  isomorphism z in GL_n(E) from a translate o·(g, α) to o acts on the parameters near 0 by a linear
  map K, and its local term, a complex polynomial p (`New.Variety.localTerm`), satisfies
  p(t) = p(0)·det(1 − tK) for all t in ℂ.

Notions from other files:
* `New.Variety.IsSignedFrameFor` g ℓ β: the adelic matrix `g` is a frame for the matrix `β` over E,
  the matrix `β.map (Φ w)` is positive definite for every infinite place `w ≠ v₀`, and
  `β.map (Φ v₀) * ℓ` is positive definite.
* `New.Variety.IsPeriodMap` ℓ Q: Q carries iℓ at v₀ and i at the other places to multiplication by
  i.
* `New.Variety.BallBase`: The complex vector space ℂ^(n−1), which contains the parameter domains of
  the families of periods.
* `New.Variety.RealVectors`: The space (E ⊗ ℝ)ⁿ, written as n-tuples of elements of the product of
  copies of ℂ over the infinite places of E.
* `New.Variety.BallFibre`: The complex space (ℂ × ℂ^(n−1)) × ∏_{v ≠ v₀} ℂⁿ, the common target of the
  period maps of a family.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

noncomputable section

/-!
## The signature of the hermitian matrix of a polarised period map

The matrix `β` over `E` of a polarised period map (`New.ThetaTori.PeriodMap`) for the frame `g` and
the complex matrix `ℓ` satisfies the sign condition `New.Variety.IsSignedFrameFor g ℓ`.
-/

section PeriodSignature

open Pi ComplexOrder New.Variety

/-- The matrix `β` of a polarised period map for `(g, ℓ)` has `g` as a frame (`gᴴ β g` is a
scalar matrix, a unit of `Ẑ`), `Φ v β` is positive definite for every infinite place `v ≠ v₀`,
and `Φ v₀ β * ℓ` is positive definite (hermitian in particular). -/
lemma New.ThetaTori.PeriodMap.isSignedFrameFor {E : Type} [Field E] [CMBase E] {V : Type}
    [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
    (x : PeriodMap D g ℓ V) :
    IsSignedFrameFor g ℓ x.formMatrix := by
  refine ⟨x.isFrameFor, fun v ↦ ?_⟩
  -- Test the Riemann form on vectors `q a` concentrated at the place `v`. There `x.realEquiv`
  -- carries `I • ite (v = v₀) ℓ 1` to multiplication by `I` and `polarisationForm` has a single
  -- term, which gives `h_riemannForm_I_smul`; symmetry and positivity of the Riemann form then pass
  -- to `H`.
  set H : Matrix D.Index D.Index ℂ := x.formMatrix.map (Φ v) * ite (v = v₀) ℓ 1 with hH
  let q (a : D.Index → ℂ) : V := x.realEquiv (Pi.single v ∘ a)
  -- `Φ v D.ξ` is purely imaginary, so `Φ v D.ξ * I = -(Φ v D.ξ).im`
  have h_riemannForm_I_smul (a b : D.Index → ℂ) :
      -(2 * ((Φ v D.ξ).im * (star a ⬝ᵥ H.mulVec b).re)) =
        x.automorphyForm.riemannForm (Complex.I • q b) (q a) := by
    have h_per :
        x.automorphyForm.riemannForm
            (x.realEquiv (Complex.I • fun i u ↦
              (if u = v₀ then ℓ else 1).mulVec
                (fun j ↦ (Pi.single v ∘ b : RealVectors E D.Index) j u) i))
            (q a) =
          x.automorphyForm.riemannForm (Complex.I • x.realEquiv (Pi.single v ∘ b)) (q a) :=
      congrArg (fun p : V ↦ x.automorphyForm.riemannForm p (q a)) (x.isPeriodMap (Pi.single v ∘ b))
    simpa +contextual [q, hH, x.riemannForm_eq, polarisationForm, Fintype.sum_eq_single v,
      ← zero_def, D.xi_im_pos_and_re_eq_zero, ← smul_def, Matrix.mulVec_smul, -smul_eq_mul,
      smul_eq_mul _ (_ ⬝ᵥ _), -mul_ite] using h_per
  -- symmetry of `Re B` makes `riemannForm (I • y) z` symmetric in `y` and `z`
  have h_symm (y z : V) :
      x.automorphyForm.riemannForm (Complex.I • y) z = x.automorphyForm.riemannForm (Complex.I • z)
        y := by
    simpa [riemannForm_def, x.re_symm] using x.re_symm (Complex.I • _) (Complex.I • _)
  have h_re (a b : D.Index → ℂ) : (star a ⬝ᵥ H.mulVec b).re = (star b ⬝ᵥ H.mulVec a).re := by
    simpa [← h_riemannForm_I_smul, ne_of_gt, D.xi_im_pos_and_re_eq_zero] using h_symm (q b) (q a)
  -- test `h_re` on multiples of two basis vectors
  have h_herm : H.IsHermitian := by
    refine .ext fun i j ↦ ext_inner_right ℝ fun c ↦ ?_
    simpa using h_re (Pi.single j 1) (Pi.single i c)
  refine .of_dotProduct_mulVec_pos h_herm fun u hu ↦
    ⟨?_, (h_herm.im_star_dotProduct_mulVec_self u).symm⟩
  -- positivity of the Riemann form at `q u`, together with `0 < (Φ v D.ξ).im`
  have hq : q u ≠ 0 := by simp_all [q, funext_iff, single_apply]
  have h_form_pos : 0 < x.automorphyForm.riemannForm (q u) (Complex.I • q u) :=
    x.isPosRiemann.riemannForm_pos (q u) hq
  -- By `h_riemannForm_I_smul` and the alternation of the Riemann form, this value is
  -- `2 Im (Φ v D.ξ) re H(u, u)`.
  have h_form_eq :
      x.automorphyForm.riemannForm (q u) (Complex.I • q u) =
        2 * ((Φ v D.ξ).im * (star u ⬝ᵥ H.mulVec u).re) := by
    rw [riemannForm_swap, ← h_riemannForm_I_smul, neg_neg]
  have h_prod : 0 < (Φ v D.ξ).im * (star u ⬝ᵥ H.mulVec u).re := by
    rw [h_form_eq] at h_form_pos
    linarith
  simpa using pos_of_mul_pos_right h_prod (D.xi_im_pos v).le

end PeriodSignature

/-!
## Analytic families of theta tori and analytic theta coordinates

A theta torus (`New.ThetaTori.ThetaTorus`) has a period map Q onto V, a form B and lattices
`New.ThetaTori.PeriodMap.latticeOver` S. Its theta functions for the lattice over S = `D.lagrangian`
are the multiples of one function, chosen for each b with no regularity in b, and
`New.ThetaTori.PeriodMap.thetaCoord` lists its normalised translates by t ∈ T. The factor c(b)
replaces the chosen function by a Poincaré series (`New.IsAppellHumbert.poincareSeries`), which does
depend analytically on b.
-/

namespace New.Variety

open ThetaTori PeriodMap IsAppellHumbert

variable {E : Type} [Field E] [CMBase E] {D : PEL E}

/-- A family of theta tori with fixed frame g over a parameter domain U = `domain` in ℂ^(n−1). The
periods are analytic, and their differential is injective modulo ℂ-linear maps. The matrix β and the
forms B(Q·, ·) are constant, and Re B is positive definite. -/
structure AnalyticFamily (D : PEL E) where
  /-- The parameter domain, an open subset of ℂⁿ⁻¹. -/
  domain : TopologicalSpace.Opens (BallBase D.Index)
  /-- The domain is non-empty and connected. -/
  isConnected : IsConnected domain.1
  /-- The adelic frame g, the same for all members of the family. -/
  frame : GL D.Index (𝔸f E)
  /-- The reflection J_b attached to the parameter b. -/
  reflection : BallBase D.Index → Matrix D.Index D.Index ℂ
  /-- The theta torus of the point (g, J_b), with period map Q_b onto the fixed space
  V = `New.Variety.BallFibre`. -/
  torus (b : BallBase D.Index) : ThetaTorus D frame (reflection b) (BallFibre E D.Index)
  /-- For each vector w, the period b ↦ Q_b w is analytic at every point of the domain. -/
  analyticAt : ∀ b₀ ∈ domain, ∀ w : RealVectors E D.Index, AnalyticAt ℂ (torus · |>.realEquiv w) b₀
  /-- On the domain, the derivative of Q in the direction v is complex linear for the complex
  structure given by Q_b only if v = 0. -/
  eq_zero_of_linear : ∀ b ∈ domain, ∀ v : BallBase D.Index,
    let d (y : BallFibre E D.Index) := fderiv ℂ (torus · |>.realEquiv ((torus b).realEquiv.symm y))
      b v
    (∀ y : BallFibre E D.Index, d (Complex.I • y) = Complex.I • d y) → v = 0
  /-- The matrix β over E and the complex linear forms B(Q_b w, ·) on V do not depend on b. -/
  form_const (b' b : BallBase D.Index) :
      (torus b).formMatrix = (torus b').formMatrix ∧
      ∀ w : RealVectors E D.Index, (torus b).automorphyForm ((torus b).realEquiv w) =
        (torus b').automorphyForm ((torus b').realEquiv w)
  /-- For every b, the real part of B(u, u) is positive for u ≠ 0. -/
  re_pos (b : BallBase D.Index) : ∀ u ≠ (0 : BallFibre E D.Index),
    0 < ((torus b).automorphyForm u u).re

attribute [local fun_prop] analyticAt_fst analyticAt_snd ContinuousLinearMap.analyticAt

/-- Let `c b • φ b` be a family of functions whose value at `(b, z)` is analytic in `(b, z)` at
`(b₀, w)` and nonzero there. Then `c b` is a unit for all `b` near `b₀`. -/
private lemma eventually_isUnit_of_analyticAt_of_apply_ne_zero {c : BallBase D.Index → ℂ}
    {φ : BallBase D.Index → BallFibre E D.Index → ℂ} {b₀ : BallBase D.Index}
    {w : BallFibre E D.Index}
    (h_an : AnalyticAt ℂ (fun p : BallBase D.Index × BallFibre E D.Index ↦ (c p.1 • φ p.1) p.2)
      (b₀, w))
    (h_ne : (c b₀ • φ b₀) w ≠ 0) :
    ∀ᶠ b : BallBase D.Index in nhds b₀, IsUnit (c b) := by
  -- The value at `w` is continuous in `b`, so it stays nonzero near `b₀`.
  have h_near : ∀ᶠ b : BallBase D.Index in nhds b₀, (c b • φ b) w ≠ 0 :=
    h_an.curry_left.continuousAt.eventually_ne h_ne
  exact h_near.mono fun b hb ↦ (left_ne_zero_of_smul hb).isUnit

/-- Let f be an analytic family of theta tori, b₀ in its domain, and θ_t(b, ·) (t ∈ T) the theta
coordinates of the member b, functions on V. There is a function c of b such that
(a) for each t, the function (b, z) ↦ c(b)·θ_t(b, z) is analytic at every point (b₀, z);
(b) c(b) ≠ 0 for b near b₀.
The factor is the same for all t and z, so the projective point (θ_t(b, z))_t is unchanged. -/
lemma AnalyticFamily.exists_analytic_thetaCoord (f : AnalyticFamily D) {b₀ : BallBase D.Index}
    (hb₀ : b₀ ∈ f.domain) :
    ∃ c : BallBase D.Index → ℂ,
      (∀ (z : BallFibre E D.Index) (t : D.dualTorsion),
        AnalyticAt ℂ
          (fun p : BallBase D.Index × BallFibre E D.Index ↦
            (c p.1 • fun s : D.dualTorsion ↦ (f.torus p.1).thetaCoord s p.2) t)
          (b₀, z)) ∧
      ∀ᶠ b : BallBase D.Index in nhds b₀, IsUnit (c b) := by
  -- The theta functions of the member `b` are multiples of its generator `φ b`. So a Poincaré
  -- series of `b` is `c b • φ b`; moved to the fixed lattice of `b₀` it is a series with
  -- parameters analytic in `b`, and it is not zero at `b₀`.
  let Q (b : BallBase D.Index) : BallFibre E D.Index ≃L[ℝ] BallFibre E D.Index :=
    (f.torus b₀).realEquiv.symm.trans (f.torus b).realEquiv
  let φ (b : BallBase D.Index) : BallFibre E D.Index → ℂ := (f.torus b).lagrangianTheta
  -- A point `w` where the Poincaré series of `b₀` does not vanish.
  obtain ⟨w, hw⟩ : ∃ w : BallFibre E D.Index,
      (f.torus b₀).isAppellHumbert_latticeOver_lagrangian.poincareSeries w w ≠ 0 := by
    obtain ⟨-, -, -, -, h_nonzero⟩ :=
      (f.torus b₀).isAppellHumbert_latticeOver_lagrangian.poincareSeries_mem_thetaSpace_and_quotMean
        (f.re_pos b₀)
    exact h_nonzero
  have h_mult (b : BallBase D.Index) : ∃ c : ℂ,
      c • φ b = (f.torus b).isAppellHumbert_latticeOver_lagrangian.poincareSeries (Q b w) := by
    obtain ⟨-, -, h_theta, -⟩ :=
      (f.torus b).isAppellHumbert_latticeOver_lagrangian.poincareSeries_mem_thetaSpace_and_quotMean
        (f.re_pos b)
    exact (f.torus b).exists_smul_lagrangianTheta_eq (h_theta (Q b w))
  choose c hc using h_mult
  have hQ_an (y : RealVectors E D.Index) (z : BallFibre E D.Index) :
      AnalyticAt ℂ (fun p : BallBase D.Index × BallFibre E D.Index ↦ (f.torus p.1).realEquiv y)
        (b₀, z) :=
    (f.analyticAt b₀ hb₀ y).comp_of_eq analyticAt_fst rfl
  -- The comparison map `Q b` carries the lattice of `b₀` onto that of `b`.
  have h_latt (b : BallBase D.Index) (x : BallFibre E D.Index) :
      x ∈ (f.torus b₀).latticeOver D.lagrangian ↔
        (Q b).toEquiv x ∈ (f.torus b).latticeOver D.lagrangian := by
    simp [Q, mem_classLattice, ContinuousLinearEquiv.eq_symm_apply]
  -- The series over the lattice of `b₀`, with `B` and `multiplier` of `b₀`; only `Q b` depends on
  -- `b`.
  let term (p : BallBase D.Index × BallFibre E D.Index)
      (l : (f.torus b₀).latticeOver D.lagrangian) : ℂ :=
    ((f.torus b₀).automorphyForm w (p.2 - Q p.1 w + Q p.1 l) - (f.torus b₀).automorphyForm l p.2 -
      (f.torus b₀).automorphyForm l (Q p.1 l) / 2).exp / (f.torus b₀).multiplier l
  have h_series_an (z : BallFibre E D.Index) :
      AnalyticAt ℂ (fun p : BallBase D.Index × BallFibre E D.Index ↦ ∑' l, term p l) (b₀, z) := by
    have hQ : ∀ᶠ b : BallBase D.Index in nhds b₀, ∀ x : BallFibre E D.Index,
        AnalyticAt ℂ (fun b' : BallBase D.Index ↦ (Q b').toContinuousLinearMap x) b :=
      (f.domain.isOpen.eventually_mem hb₀).mono fun b hb x ↦ f.analyticAt b hb _
    have h_pos (x : BallFibre E D.Index) (hx : x ≠ 0) :
      0 < ((f.torus b₀).automorphyForm x (Q b₀ x)).re := by
      simp [Q, re_pos, hx]
    have h_param : AnalyticAt ℂ (fun p ↦ (p.1, (f.torus b₀).automorphyForm w, p.2 - Q p.1 w, p.2))
      (b₀, z) := by
      dsimp [Q]
      fun_prop
    -- A theta series with positive quadratic part is analytic in all its parameters.
    obtain ⟨-, h_sum_an⟩ :=
      (f.torus b₀).isAppellHumbert_latticeOver_lagrangian.summable_and_analyticAt_tsum hQ h_pos
        ((f.torus b₀).automorphyForm w, z - Q b₀ w, z)
    exact (h_sum_an.comp_of_eq h_param rfl).congr .rfl
  -- Term by term it is the Poincaré series of `b`, as `β` and `B (Q ·)` are free of `b`
  -- (`f.form_const`).
  have h_series_eq (p : BallBase D.Index × BallFibre E D.Index) :
      ∑' l, term p l = (c p.1 • φ p.1) p.2 := by
    have h_term : ∀ l : (f.torus b₀).latticeOver D.lagrangian, term p l =
        (f.torus p.1).isAppellHumbert_latticeOver_lagrangian.poincareTerm (Q p.1 w) p.2
          ((Q p.1).toEquiv.subtypeEquiv (h_latt p.1) l) := by
      simp [term, Q, poincareTerm, f.form_const b₀, canonicalMultiplier, intAction,
        riemannForm_eq, mem_classLattice]
    calc
      _ = (f.torus p.1).isAppellHumbert_latticeOver_lagrangian.poincareSeries (Q p.1 w) p.2 := by
        rw [tsum_congr h_term, Equiv.tsum_eq, poincareSeries]
      _ = _ := by rw [hc]
  have h_lift_an (z : BallFibre E D.Index) : AnalyticAt ℂ (fun p ↦ (c p.1 • φ p.1) p.2) (b₀, z) :=
    (h_series_an z).congr (.of_forall h_series_eq)
  refine ⟨c, fun z t ↦ ?_, ?_⟩
  · -- `thetaCoord t` is a translate of `φ b` by a vector analytic in `b`, times a constant and an
    -- exponential.
    simp [thetaCoord, normalizedShift, PeriodMap.torsionLift, thetaShift, f.form_const b₀,
      canonicalMultiplier, intAction, riemannForm_eq, mul_left_comm (c _)]
    -- The goal is a constant times an exponential in `p` times `c p.1 • φ p.1` at a translate.
    refine AnalyticAt.mul ?_ (AnalyticAt.mul ?_ ?_)
    · fun_prop
    · fun_prop
    · exact (h_lift_an _).comp₂ analyticAt_fst (analyticAt_snd.add (hQ_an _ z))
  · -- The value of `c b • φ b` at `w` is continuous in `b` and not zero at `b₀`.
    have h_ne : (c b₀ • φ b₀) w ≠ 0 := by
      rw [hc]
      simpa [Q] using hw
    exact eventually_isUnit_of_analyticAt_of_apply_ne_zero (h_lift_an w) h_ne

end New.Variety

/-!
## The ball chart of moduli points with a given frame

A point `New.Variety.ModuliPoint` is a triple (x, ℓ, P): an adelic frame x, a line in ℂⁿ, recorded
as the reflection ℓ that fixes it, and vectors P_i in (E ⊗ ℝ)ⁿ. For fixed x the frame determines a
form β, and the lines that occur are those positive for H = Φ_{v₀}(β); they form a ball in ℂ^(n−1).
-/

section BallModel

open Topology Matrix Polynomial ComplexOrder Complex LinearMap Real Fintype Finset

namespace New.Variety

section PeriodsOnTheBall

variable (E : Type)
  {n : Type} [Field E] [Ψ : CMBase E] [Fintype.{0} n] [DecidableEq n]
  {D : PEL E} (e : (n → ℂ) ≃L[ℂ] ℂ × BallBase n) (H : Matrix n n ℂ)

/-- For a continuous linear isomorphism e : ℂⁿ ≃ ℂ × ℂ^(n−1) and a complex matrix H, the map,
ℂ-linear in q = (q₁, q') and ℝ-linear in w, with value ((e⁻¹q)ᵀHw₀, q₁y₂ − y₁q', (q₁w_v)_{v≠v₀}),
where w₀ = w_{v₀} and (y₁, y₂) = e(w̄₀). -/
@[simp]
def ballPeriod : ℂ × BallBase n →ₗ[ℂ] RealVectors E n →ₗ[ℝ] BallFibre E n := by
  apply mk₂' ℂ ℝ fun q w ↦
    ((e.symm q ⬝ᵥ H *ᵥ (w · v₀)) • (1, 0) + q.1 • e (star (w · v₀)) - (e (star (w · v₀))).1 • q,
      fun v ↦ q.1 • (w · v))
  -- additive and homogeneous in `q` (over ℂ) and in `w` (over ℝ), coordinate by coordinate
  all_goals
    intros
    ext <;> simp [-smul_eq_mul, ← Pi.smul_def, smul_smul, ← Pi.add_def, mulVec_add,
      ← Complex.coe_smul, mulVec_smul] <;> ring

/-- The set of b in ℂ^(n−1) such that x = e⁻¹(1, b) in ℂⁿ is positive for H, that is, Re ∑ x_i
H_ij conj(x_j) > 0. -/
abbrev positiveBall : Set (BallBase n) :=
  {b : BallBase n | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}

/-- The matrix of w ↦ 2(uᴴHw)/(uᴴHu)·u − w; if uᴴHu ≠ 0 it fixes u and is −1 on the w with
uᴴHw = 0. -/
abbrev formReflection (u : n → ℂ) : Matrix n n ℂ :=
  vecMulVec u ((2 / star u ⬝ᵥ H *ᵥ u) • star u ᵥ* H) - 1

end PeriodsOnTheBall

variable {E : Type} {n : Type} [Field E] [Ψ : CMBase E] [Fintype.{0} n]
  {D : PEL E} (e : (n → ℂ) ≃L[ℂ] ℂ × BallBase n) {H : Matrix n n ℂ}

/-- If H is Hermitian, J is a reflection (J = u wᵀ − 1 for vectors u, w with w ⬝ᵥ u = 2) and HJ is
positive definite, then J is the reflection for the form H in a vector u with uᴴHu > 0. -/
lemma exists_eq_formReflection [DecidableEq n]
    (hH : H.IsHermitian) {J : Matrix n n ℂ} (hHJ : (H * J).PosDef)
    (hJ : IsReflection J) : ∃ u : n → ℂ, 0 < star u ⬝ᵥ H *ᵥ u ∧ J = formReflection H u := by
  -- Put `H(a, b) = star a ⬝ᵥ H *ᵥ b` and write `J = u wᵀ - 1` with `w ⬝ᵥ u = 2`, so that
  -- `J u = u`. Positivity of `H * J` at `u` gives `H(u, u) > 0`, and its symmetry determines
  -- `w`: `w ⬝ᵥ x = 2 H(u, x) / H(u, u)`.
  obtain ⟨u, w, hwu, rfl⟩ := hJ
  have h_fix : (vecMulVec u w - 1) *ᵥ u = u := by simp [hwu, two_smul, sub_mulVec, vecMulVec_mulVec]
  have h_u_ne : u ≠ 0 := by aesop
  have h_pos : 0 < star u ⬝ᵥ H *ᵥ u := by
    simpa only [← mulVec_mulVec, h_fix] using hHJ.dotProduct_mulVec_pos h_u_ne
  -- As `H` and `H * J` are Hermitian, `H(u, x) = H(u, J x) = (w ⬝ᵥ x) H(u, u) - H(u, x)`.
  have h_symm (x : n → ℂ) : star u ⬝ᵥ H *ᵥ x = w ⬝ᵥ x * star u ⬝ᵥ H *ᵥ u - star u ⬝ᵥ H *ᵥ x := by
    simpa [h_fix, star_dotProduct_mulVec_comm hH, ← mulVec_mulVec, sub_mulVec, vecMulVec_mulVec,
      mulVec_sub,
      mulVec_smul] using star_dotProduct_mulVec_comm hHJ.1 x u
  have h_w : w = (2 / star u ⬝ᵥ H *ᵥ u) • star u ᵥ* H := dotProduct_eq _ _ fun x ↦ by
    grind [smul_dotProduct, dotProduct_mulVec, smul_eq_mul]
  exact ⟨u, h_pos, by rw [h_w]⟩

/-- Write `H(a, c) = star a ⬝ᵥ H *ᵥ c`. Let `H` be Hermitian, negative definite on the
hyperplane `(e (star y)).1 = 0` and positive at `star x`, `x = e.symm (1, b)`. Then
`re H(y, y) < 2 re (s * H(star x, y))` for `y ≠ 0`, where `s = (e (star y)).1`. -/
lemma re_form_lt_of_mem_positiveBall (hH : H.IsHermitian)
    (hneg : ∀ y ≠ (0 : n → ℂ), (e (star y)).1 = 0 → star y ⬝ᵥ H *ᵥ y < 0) {b : BallBase n}
    (hb : b ∈ positiveBall e H) {y : n → ℂ} (hy : y ≠ 0) :
    (star y ⬝ᵥ H *ᵥ y).re < 2 * ((e (star y)).1 * (e.symm (1, b) ⬝ᵥ H *ᵥ y)).re := by
  set s : ℂ := (e (star y)).1 with hs
  set x : n → ℂ := e.symm (1, b) with hx
  -- The vector `y' = y - star (s • x)` lies in the hyperplane, so `re H(y', y') < 0` if `y' ≠ 0`;
  -- if `y' = 0` then `s ≠ 0`, and the right side below is positive.
  let y' : n → ℂ := y - star (s • x)
  have y'_lt : (star y' ⬝ᵥ H *ᵥ y').re < normSq s * (x ⬝ᵥ H *ᵥ star x).re := by
    by_cases h : y' = 0
    · have h_s_ne : s ≠ 0 := fun hs₀ ↦ hy (by simpa [y', hs₀] using h)
      simpa [h] using mul_pos (normSq_pos.mpr h_s_ne) hb
    · have h_neg : star y' ⬝ᵥ H *ᵥ y' < 0 := hneg y' h (by simp [y', hx, ← hs])
      exact (Complex.lt_def.1 h_neg).left.trans_le (mul_nonneg s.normSq_nonneg hb.le)
  have h_expand :
      (star y' ⬝ᵥ H *ᵥ y').re =
        (star y ⬝ᵥ H *ᵥ y).re - 2 * (s * (x ⬝ᵥ H *ᵥ y)).re + normSq s * (x ⬝ᵥ H *ᵥ star x).re := by
    simp [y', normSq, ← star_dotProduct_mulVec_comm hH (star x), mulVec_sub, mulVec_smul]
    ring
  linarith

/-- The form at the infinite place v from which `exists_form_along_ballPeriod` builds its form: the
map (w, p) ↦ 2π Im Φ_v(ξ) · F_v(w, p), ℝ-linear in w ∈ (E ⊗ ℝ)ⁿ and ℂ-linear in p ∈ `BallFibre`,
where F_{v₀}(w, p) = (e(w̄_{v₀}))₁ p₁₁ − (e⁻¹(p₁ − p₁₁ (1, 0)))ᵀ H w_{v₀}, p₁ ∈ ℂ × ℂ^(n−1) being
the first component of p and p₁₁ its first coordinate, and F_v(w, p) = w̄_vᵀ Φ_v(β) p₂(v) for v ≠
v₀. -/
private def ballFormAt (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index)
    (H : Matrix D.Index D.Index ℂ) (β : Matrix D.Index D.Index E)
    (v : NumberField.InfinitePlace E) :
    RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index →ₗ[ℂ] ℂ := by
  apply mk₂' ℝ ℂ fun w p ↦ 2 * π * (Φ v D.ξ).im *
    if h : v = v₀ then
      (e (star (w · v))).1 * p.1.1 - e.symm (p.1 - p.1.1 • (1, 0)) ⬝ᵥ H *ᵥ (w · v)
    else star (w · v) ⬝ᵥ β.map (Φ v) *ᵥ p.2 ⟨v, h⟩
  -- additive and homogeneous in `w` (over ℝ) and in `p` (over ℂ), in each of the two cases
  all_goals as_aux_lemma =>
    intros
    split <;> simp [-smul_eq_mul, -Prod.smul_mk, ← Pi.add_def, mulVec_add, ← Complex.coe_smul,
      ← Pi.smul_def, mulVec_smul, smul_smul] <;> ring

/-- The value of `ballFormAt e H β v` at w = y on the periods P_b z = `ballPeriod E e H (1, b) z`:
2π Im Φ_v(ξ) times, at v = v₀, s_y H(x, z) + s_z H(x, y) − H(z̄, y), where y and z stand for
y_{v₀} and z_{v₀}, x = e⁻¹(1, b), s_y = (e(ȳ_{v₀}))₁ and H(a, c) = aᵀ H c; and times
ȳ_vᵀ Φ_v(β) z_v at v ≠ v₀. -/
private lemma ballFormAt_ballPeriod (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index)
    (H : Matrix D.Index D.Index ℂ) (β : Matrix D.Index D.Index E) (b : BallBase D.Index)
    (v : NumberField.InfinitePlace E) (y z : RealVectors E D.Index) :
    ballFormAt e H β v y (ballPeriod E e H (1, b) z) = 2 * π * (Φ v D.ξ).im *
      if v = v₀ then
        (e (star (y · v))).1 * (e.symm (1, b) ⬝ᵥ H *ᵥ (z · v)) +
          (e (star (z · v))).1 * (e.symm (1, b) ⬝ᵥ H *ᵥ (y · v)) - star (z · v) ⬝ᵥ H *ᵥ (y · v)
      else star (y · v) ⬝ᵥ β.map (Φ v) *ᵥ (z · v) := by
  by_cases h : v = v₀
  · simp [ballFormAt, h, -smul_eq_mul, -mul_eq_mul_left_iff, -Prod.smul_mk]
    ring
  · simp [ballFormAt, h, -smul_eq_mul, -mul_eq_mul_left_iff, -Prod.smul_mk]

/-- Riemann relations along the periods. Assume `IsSignedFrameFor g ℓ β`: `g` is a frame for `β`,
`β` is positive definite at every place `w ≠ v₀`, and `Φ v₀ β * ℓ` is positive definite. Let
H = Φ_{v₀}(β) be negative definite on the y ≠ 0 with `(e (star y)).1 = 0`. Write
P_b = `ballPeriod E e H (1, b)` for the period map at b ∈ ℂ^(n−1). Then some A(w, p), ℝ-linear in
w ∈ (E ⊗ ℝ)ⁿ and ℂ-linear in p ∈ `BallFibre E D.Index`, has: (a) Re A(w, P_b w) > 0 for b in
`positiveBall e H`, w ≠ 0; (b) A(y, P_b z) − A(z, P_b y) = 2πi · `polarisationForm D β` y z, which
equals 2πi ∑_v 2 Re(Φ_v(ξ) z̄_vᵀ Φ_v(β) y_v), for all b; (c) A(c y, P_b z) = A(y, P_b (c̄ z)) for c
in E acting through the CM embedding. -/
lemma exists_form_along_ballPeriod (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index)
    {H : Matrix D.Index D.Index ℂ}
    (hneg : ∀ y ≠ (0 : D.Index → ℂ), (e (star y)).1 = 0 → star y ⬝ᵥ H *ᵥ y < 0)
    {ℓ : Matrix D.Index D.Index ℂ} {g : GL D.Index (𝔸f E)} {β : Matrix D.Index D.Index E}
    (hβ : IsSignedFrameFor g ℓ β) (hH : β.map (Φ v₀) = H) :
    ∃ A : RealVectors E D.Index →L[ℝ] BallFibre E D.Index →L[ℂ] ℂ,
      (∀ b ∈ positiveBall e H, ∀ w ≠ (0 : RealVectors E D.Index),
        0 < (A w (ballPeriod E e H (1, b) w)).re) ∧
      (∀ (b : BallBase D.Index) (y z : RealVectors E D.Index),
        A y (ballPeriod E e H (1, b) z) - A z (ballPeriod E e H (1, b) y) =
          2 * π * Complex.I * polarisationForm D β y z) ∧
      ∀ (b : BallBase D.Index) (c : E) (y z : RealVectors E D.Index),
        A (cmEmbedding c • y) (ballPeriod E e H (1, b) z) =
          A y (ballPeriod E e H (1, b) (cmEmbedding (star c) • z)) := by
  -- Take `A = ∑ v, f v` with `f = ballFormAt e H β`. At `v ≠ v₀` the term `f v` is a positive
  -- multiple of the Hermitian form of `β`; at `v₀` it is chosen so that `f_P` below holds.
  let f (v : NumberField.InfinitePlace E) :
      RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index →ₗ[ℂ] ℂ :=
    ballFormAt e H β v
  let A : RealVectors E D.Index →L[ℝ] BallFibre E D.Index →L[ℂ] ℂ :=
    (restrictScalars ℝ toContinuousLinearMap.toLinearMap ∘ₗ ∑ v, f v).toContinuousLinearMap
  have h_A (y : RealVectors E D.Index) (p : BallFibre E D.Index) : A y p = ∑ v, f v y p := by
    simp [A]
  let P (b : BallBase D.Index) : RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index :=
    ballPeriod E e H (1, b)
  have f_P (b : BallBase D.Index) (v : NumberField.InfinitePlace E) (y z : RealVectors E D.Index) :
      f v y (P b z) = 2 * π * (Φ v D.ξ).im *
      if v = v₀ then
        (e (star (y · v))).1 * (e.symm (1, b) ⬝ᵥ H *ᵥ (z · v)) +
          (e (star (z · v))).1 * (e.symm (1, b) ⬝ᵥ H *ᵥ (y · v)) - star (z · v) ⬝ᵥ H *ᵥ (y · v)
      else star (y · v) ⬝ᵥ β.map (Φ v) *ᵥ (z · v) :=
    ballFormAt_ballPeriod e H β b v y z
  obtain ⟨h_frame, h_posDef⟩ : IsFrameFor β g ∧
      ∀ v : NumberField.InfinitePlace E, (β.map (Φ v) * if v = v₀ then ℓ else 1).PosDef := hβ
  have h_herm_H : H.IsHermitian := by
    rw [← hH]
    exact h_frame.isHermitian_map
  refine ⟨A, fun b hb w hw ↦ ?_, fun b y z ↦ ?_, fun b c y z ↦ ?_⟩
  · -- The real part of the term at `v` is positive if `w` does not vanish at `v`, and the term is
    -- zero otherwise.
    have term_pos (v : NumberField.InfinitePlace E) (hv : (w · v) ≠ 0) :
        0 < (f v w (P b w)).re := by
      by_cases h : v = v₀
      · subst h
        simpa [f_P, pi_pos, two_mul, PEL.xi_im_pos_and_re_eq_zero] using
          re_form_lt_of_mem_positiveBall e h_herm_H hneg hb hv
      · simpa [f_P, h, pi_pos, PEL.xi_im_pos_and_re_eq_zero] using
          (h_posDef v).re_dotProduct_pos hv
    have term_nonneg (v : NumberField.InfinitePlace E) : 0 ≤ (f v w (P b w)).re := by
      by_cases hv : (w · v) = 0
      · simp [f, ballFormAt, hv]
      · exact (term_pos v hv).le
    -- `w ≠ 0` does not vanish at some place, where its term is positive.
    obtain ⟨v, hv⟩ : ∃ v : NumberField.InfinitePlace E, (w · v) ≠ 0 :=
      Function.ne_iff.1 (mt transpose_eq_zero.1 hw)
    rw [h_A, Complex.re_sum]
    exact sum_pos' (fun u _ ↦ term_nonneg u) ⟨v, mem_univ v, term_pos v hv⟩
  · -- Place by place: the terms with `e.symm (1, b)` are symmetric in `y`, `z` and cancel;
    -- `star a - a` is left, for `a` the Hermitian form at `v`, and `Φ v D.ξ` is purely imaginary.
    have term (v : NumberField.InfinitePlace E) :
        f v y (P b z) - f v z (P b y) = 2 * π * Complex.I *
          (2 * (Φ v D.ξ * star (z · v) ⬝ᵥ β.map (Φ v) *ᵥ (y · v)).re : ℝ) := by
      set a : ℂ := star (z · v) ⬝ᵥ β.map (Φ v) *ᵥ (y · v) with ha
      have diff : f v y (P b z) - f v z (P b y) = 2 * π * (Φ v D.ξ).im * (star a - a) := by
        rw [f_P, f_P, ha, star_dotProduct_mulVec_comm h_frame.isHermitian_map]
        split_ifs with h
        · rw [h, hH]
          ring
        · ring
      simp [diff, Complex.ext_iff, PEL.xi_im_pos_and_re_eq_zero]
      ring
    rw [h_A, h_A, ← sum_sub_distrib, sum_congr rfl fun v _ ↦ term v]
    simp [polarisationForm, mul_sum]
  · -- Each term of `f_P` is linear in one of `y`, `z` and antilinear in the other.
    rw [h_A, h_A]
    refine sum_congr rfl fun v _ ↦ ?_
    rw [f_P, f_P]
    by_cases h_v : v = v₀ <;> simp [h_v, -smul_eq_mul, ← Pi.smul_def, mulVec_smul]

/-- A nonempty set `S` is the range of a map `r` that fixes every point of `S`. -/
lemma _root_.Set.Nonempty.exists_retraction {α : Type*} {S : Set α} (hS : S.Nonempty) :
    ∃ r : α → α, (∀ b : α, r b ∈ S) ∧ ∀ b ∈ S, r b = b := by
  classical
  obtain ⟨b₀, hb₀⟩ := hS
  exact ⟨fun b ↦ if b ∈ S then b else b₀, fun b ↦ by grind, fun b hb ↦ ite_eq_left hb⟩

/-- A real linear map `P` from (E ⊗ ℝ)ⁿ to the fibre `New.Variety.BallFibre` is injective if a form
`A` has Re A(w, P w) > 0 for every w ≠ 0. -/
private lemma injective_of_re_pos {P : RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index}
    {A : RealVectors E D.Index →L[ℝ] BallFibre E D.Index →L[ℂ] ℂ}
    (hA : ∀ w ≠ 0, 0 < (A w (P w)).re) : Function.Injective P := by
  refine (injective_iff_map_eq_zero P).2 fun w hw ↦ by_contra fun hw_ne ↦ ?_
  simpa [hw] using hA w hw_ne

/-- If a form `A` has Re A(w, P w) > 0 for every w ≠ 0 and the real isomorphism `Q` agrees with
`P`, then the form B = A ∘ Q⁻¹ on the fibre has Re B(u, u) > 0 for every u ≠ 0. -/
private lemma re_comp_symm_apply_self_pos {P : RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index}
    {Q : RealVectors E D.Index ≃L[ℝ] BallFibre E D.Index}
    (hQ : ∀ w : RealVectors E D.Index, Q w = P w)
    {A : RealVectors E D.Index →L[ℝ] BallFibre E D.Index →L[ℂ] ℂ}
    (hA : ∀ w ≠ 0, 0 < (A w (P w)).re) :
    ∀ u ≠ 0, 0 < ((A ∘L Q.symm) u u).re := by
  intro u hu
  simpa [← hQ] using hA (Q.symm u) (by simpa using hu)

/-- The period b ↦ `ballPeriod E e H (1, b) w` is affine in b; its derivative is v ↦
`ballPeriod E e H (0, v) w`. -/
private lemma hasFDerivAt_ballPeriod (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index)
    (H : Matrix D.Index D.Index ℂ) (w : RealVectors E D.Index) (b : BallBase D.Index) :
    HasFDerivAt (fun b' : BallBase D.Index ↦ ballPeriod E e H (1, b') w)
      (((ballPeriod E e H).flip w).toContinuousLinearMap ∘L .inr ℂ ℂ (BallBase D.Index)) b :=
  (ContinuousLinearMap.hasFDerivAt ((ballPeriod E e H).flip w).toContinuousLinearMap).comp b
    (hasFDerivAt_prodMk_right (1 : ℂ) b)

/-- The real vector spaces (E ⊗ ℝ)ⁿ and `New.Variety.BallFibre E D.Index` have the same
dimension. -/
lemma finrank_realVectors_eq_finrank_ballFibre :
    Module.finrank ℝ (RealVectors E D.Index) = Module.finrank ℝ (BallFibre E D.Index) := by
  zify
  simp [Fin.pos', finrank_real_of_complex, Module.finrank_pi_fintype]
  ring

/-- Let x = e⁻¹(1, b) have xᵀHx̄ ≠ 0, and let the real isomorphism `Q` agree with
`New.Variety.ballPeriod` at (1, b). Then `Q` is a period map (`New.Variety.IsPeriodMap`) for the
reflection `New.Variety.formReflection` for H in x̄. -/
private lemma isPeriodMap_formReflection_of_apply_eq_ballPeriod
    (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index) {H : Matrix D.Index D.Index ℂ}
    {b : BallBase D.Index} (hx : e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b)) ≠ 0)
    {Q : RealVectors E D.Index ≃L[ℝ] BallFibre E D.Index}
    (hQ : ∀ w : RealVectors E D.Index, Q w = ballPeriod E e H (1, b) w) :
    IsPeriodMap (formReflection H (star (e.symm (1, b)))) Q := by
  simp_all [IsPeriodMap, funext_iff, -smul_eq_mul, -Prod.smul_mk, -Pi.star_apply, ← Pi.sub_def,
    sub_mulVec, mulVec_smul, smul_mulVec, ← Pi.smul_def, Prod.ext_iff, vecMulVec_mulVec,
    ← dotProduct_mulVec, smul_smul, mulVec_sub]
  grind [smul_eq_mul]

open ThetaTori in
/-- Let `positiveBall e H` (the b with x = e⁻¹(1, b) satisfying Re ∑ x_i H_ij x̄_j > 0) be
connected. Let H = β.map (Φ v₀) be negative on the y ≠ 0 with (e ȳ).1 = 0, and let g be a frame for
β with β.map (Φ w) positive definite for every infinite place w ≠ v₀ and H * ℓ positive definite
(`IsSignedFrameFor g ℓ β`). Then some analytic family has domain `positiveBall e H` and frame g, and
at each b its reflection is `formReflection H u` for u = conj e⁻¹(1, b), and the period map of its
torus is `ballPeriod E e H (1, b)`: ℂ-linear in q, ℝ-linear in w, with value ((e⁻¹q)ᵀHw₀,
q₁y₂ − y₁q', (q₁w_v)_{v≠v₀}), where (y₁, y₂) = e(w̄₀). -/
lemma exists_analyticFamily_positiveBall (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index)
    {H : Matrix D.Index D.Index ℂ} (hS : IsConnected (positiveBall e H))
    (hneg : ∀ y ≠ (0 : D.Index → ℂ), (e (star y)).fst = 0 → star y ⬝ᵥ H *ᵥ y < 0)
    {ℓ : Matrix D.Index D.Index ℂ} {g : GL D.Index (𝔸f E)} {β : Matrix D.Index D.Index E}
    (hβ : IsSignedFrameFor g ℓ β) (hH : β.map (Φ v₀) = H) :
    ∃ f : AnalyticFamily D,
      f.domain.carrier = positiveBall e H ∧
      f.frame = g ∧
      ∀ b ∈ f.domain,
        f.reflection b = formReflection H (star (e.symm (1, b))) ∧
        ⇑(f.torus b).realEquiv = ⇑(ballPeriod E e H (1, b)) := by
  -- The polarisation at `b` is the form `A` of `exists_form_along_ballPeriod`, read through the
  -- periods.
  obtain ⟨A, A_pos, A_alt, A_adj⟩ := exists_form_along_ballPeriod (D := D) e hneg hβ hH
  have ball_open : IsOpen (positiveBall e H) := isOpen_lt (by fun_prop) (by fun_prop)
  -- `r` is a retraction onto the ball, to have periods `P b` for all `b`.
  obtain ⟨r, hr, hr_eq⟩ := hS.nonempty.exists_retraction
  let x (b : BallBase D.Index) : D.Index → ℂ := e.symm (1, r b)
  have x_ne (b : BallBase D.Index) : x b ⬝ᵥ H *ᵥ star (x b) ≠ 0 := ne_zero_of_re_pos (hr b)
  let P (b : BallBase D.Index) : RealVectors E D.Index →ₗ[ℝ] BallFibre E D.Index :=
    ballPeriod E e H (1, r b)
  have hP_pos (b : BallBase D.Index) : ∀ w ≠ 0, 0 < (A w (P b w)).re := A_pos _ (hr b)
  -- By positivity of `A` the map `P b` is injective, so it is an isomorphism by dimension.
  have P_inj (b : BallBase D.Index) : Function.Injective (P b) := injective_of_re_pos (hP_pos b)
  let Q (b : BallBase D.Index) : RealVectors E D.Index ≃L[ℝ] BallFibre E D.Index :=
    ((P b).linearEquivOfInjective (P_inj b) finrank_realVectors_eq_finrank_ballFibre)
      |>.toContinuousLinearEquiv
  have hQ (b : BallBase D.Index) (w : RealVectors E D.Index) : Q b w = P b w := rfl
  have hper (b : BallBase D.Index) : IsPeriodMap (formReflection H (star (x b))) (Q b) :=
    isPeriodMap_formReflection_of_apply_eq_ballPeriod e (x_ne b) (hQ b)
  -- On the ball `Q b w = ballPeriod E e H (1, b) w` is affine in `b`.
  have hderiv {w : RealVectors E D.Index} (b : BallBase D.Index) (hb : b ∈ positiveBall e H) :
      HasFDerivAt (fun b' : BallBase D.Index ↦ Q b' w)
        (((ballPeriod E e H).flip w).toContinuousLinearMap ∘L .inr ℂ ℂ (BallBase D.Index)) b := by
    refine (hasFDerivAt_ballPeriod e H w b).congr_of_eventuallyEq ?_
    filter_upwards [ball_open.mem_nhds hb] with b' hb'
    simp [hQ, P, hr_eq b' hb']
  have h_alt (b : BallBase D.Index) (y z : RealVectors E D.Index) :
      A y (Q b z) - A z (Q b y) = 2 * π * Complex.I * polarisationForm D β y z :=
    A_alt (r b) y z
  have h_adj (b : BallBase D.Index) (c : E) (y z : RealVectors E D.Index) :
      A (cmEmbedding c • y) (Q b z) = A y (Q b (cmEmbedding (star c) • z)) := A_adj (r b) c y z
  -- `c` acts on the three components of the periods by `Φ v₀ c`, its conjugate and the `Φ v c`.
  have h_smul (b : BallBase D.Index) (c : E) (w : RealVectors E D.Index) :
      Q b (cmEmbedding c • w) =
        ((Φ v₀ c • (Q b w).1.1, star (Φ v₀ c) • (Q b w).1.2),
          fun v ↦ Φ v.val c • (Q b w).2 v) := by
    simp [hQ, P, mulVec_smul, -smul_eq_mul, ← Pi.smul_def, smul_smul, Prod.ext_iff]
    simp [funext_iff, field, smul_sub, smul_smul]
  have h_pos (b : BallBase D.Index) : ∀ u ≠ 0, 0 < ((A ∘L (Q b).symm) u u).re :=
    re_comp_symm_apply_self_pos (hQ b) (hP_pos b)
  let family : AnalyticFamily D :=
    { domain := ⟨positiveBall e H, ball_open⟩
      isConnected := hS
      frame := g
      reflection b := formReflection H (star (x b))
      torus b :=
        { formMatrix := β, realEquiv := Q b
          automorphyForm := A ∘L (Q b).symm
          isFrameFor := hβ.left
          isPeriodMap := hper b
          -- the right side of `h_alt` is purely imaginary, and gives the Riemann form
          re_symm := by simp [reindex_equiv (Q b), ← sub_eq_zero, ← sub_re, h_alt, -Prod.forall]
          riemannForm_eq := by simp [riemannForm_def, h_alt, field]
          isPosRiemann := isPosRiemann_of_re_pos (h_pos b)
          reflection := ⟨star (x b), _, by simp [x_ne, ← dotProduct_mulVec], rfl⟩
          -- using! lets the two sides match after unfolding the equivalence
          adjoint c := by
            simpa [reindex_equiv (Q b), -Prod.forall, PeriodMap.intAction] using! h_adj b c
          exists_std_equiv := ⟨.refl ℂ (BallFibre E D.Index), fun a ↦ by
            simp [LinearMap.ext_iff, -Prod.forall, PeriodMap.intAction,
              h_smul, Prod.ext_iff, funext_iff]⟩ }
      analyticAt b hb w := analyticAt_of_eventually_differentiableAt
        (.mono (ball_open.mem_nhds hb) fun b' hb' ↦ (hderiv b' hb').differentiableAt)
      -- Test linearity on `Q b w` for `w` in the line of `b`: the `BallBase` component of the
      -- derivative along `v` is `-v` at this `w` and is antilinear in `w`, which forces `v = -v`.
      eq_zero_of_linear b hb v hlin := by
        let y : BallFibre E D.Index := Q b fun i _ ↦ star (x b) i
        have h_lin : (fderiv ℂ (Q · ((Q b).symm (Complex.I • y))) b v).1.2 =
            (Complex.I • fderiv ℂ (Q · ((Q b).symm y)) b v).1.2 :=
          congrArg (fun p : BallFibre E D.Index ↦ p.1.2) (hlin y)
        -- `hper ..` is the period equation of `Q b` with its vector left open, as a rewrite rule.
        simpa [y, x, x_ne, ← hper .., (hderiv b hb).fderiv, two_smul, self_eq_neg, sub_mulVec,
          mulVec_smul, smul_mulVec, -smul_eq_mul, -Pi.star_apply, ← Pi.smul_def, vecMulVec_mulVec,
          ← dotProduct_mulVec, smul_smul] using h_lin
      form_const := by simp
      re_pos := h_pos }
  exact ⟨family, rfl, rfl, fun b hb ↦ by simp [family, x, hr_eq b hb, hQ, P, funext_iff]⟩

/-- If H is hermitian and a = ūᵀHu > 0, there are linear coordinates e : ℂⁿ ≅ ℂ × ℂ^(n−1) with
a·e(y)₁ = yᵀHu and e(ū) = (1, 0). In these coordinates the b for which x = e⁻¹(1, b) has Re xᵀHx̄ >
0 form a set star-convex at 0. -/
lemma exists_ball_chart (hH : H.IsHermitian) {u : n → ℂ} {a : ℂ} (ha : star u ⬝ᵥ H *ᵥ u = a)
    (hu : 0 < a) :
    ∃ e : (n → ℂ) ≃L[ℂ] ℂ × BallBase n,
      StarConvex ℝ 0 (positiveBall e H) ∧
      (∀ y : n → ℂ, a * (e y).fst = y ⬝ᵥ H *ᵥ u) ∧
      e.symm (1, 0) = star u := by
  -- Split off the line through `star u`: the functional `y ↦ a⁻¹ * (y ⬝ᵥ H *ᵥ u)` is `1` at
  -- `star u`, and its kernel has dimension `card n - 1`.
  obtain ⟨e, he, he₀⟩ : ∃ e : (n → ℂ) ≃L[ℂ] ℂ × BallBase n,
      (∀ y : n → ℂ, a * (e y).fst = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) = star u := by
    let φ : (n → ℂ) →L[ℂ] ℂ := (a⁻¹ • (dotProductBilin ℂ ℂ).flip (H *ᵥ u)).toContinuousLinearMap
    have h_rightInv : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℂ (star u)) φ := by
      intro c
      simp [φ, ha, hu.ne']
    let j : (n → ℂ) ≃L[ℂ] ℂ × φ.ker :=
      ContinuousLinearEquiv.equivOfRightInverse φ (.toSpanSingleton ℂ (star u)) h_rightInv
    have h_rank : Module.finrank ℂ (ℂ × φ.ker) - 1 = Module.finrank ℂ (n → ℂ) - 1 :=
      congrArg (fun k : ℕ ↦ k - 1) j.finrank_eq.symm
    have rank_ker : Module.finrank ℂ φ.ker = Module.finrank ℂ (BallBase n) := by
      simpa -dsimp using h_rank
    exact ⟨j.trans (.prodCongr (.refl ℂ ℂ) (.ofFinrankEq rank_ker)), by simp -dsimp [j, φ, hu.ne']⟩
  refine ⟨e, fun b hb s t hs ht hst ↦ ?_, he, he₀⟩
  -- Put `x = e.symm (1, b)`. As `(x - star u) ⬝ᵥ H *ᵥ u = 0`, the cross terms vanish and the value
  -- of the form at `t • b` is `a + t ^ 2 * (x ⬝ᵥ H *ᵥ star x - a)`. Its real part is a convex
  -- combination of two positive numbers.
  set x : n → ℂ := e.symm (1, b) with hx
  have point_eq : e.symm (1, (t : ℂ) • b) = star u + t • (x - star u) :=
    e.injective (by simp [hx, ← he₀, ← Complex.coe_smul])
  have x_u : x ⬝ᵥ H *ᵥ u = a := by simp [hx, ← he]
  have u_x : star u ⬝ᵥ H *ᵥ star x = star a := by
    rw [← star_dotProduct_mulVec_comm hH (star x), star_star, x_u]
  have ha_re : 0 < a.re := (Complex.lt_def.1 hu).1
  have convex : 0 < a.re + t ^ 2 * ((x ⬝ᵥ H *ᵥ star x).re - a.re) :=
    (convex_Ioi 0).add_smul_sub_mem ha_re hb ⟨sq_nonneg t, by bound⟩
  simp [point_eq, ha, x_u, u_x, ← Complex.coe_smul, mulVec_add, mulVec_smul, mulVec_sub]
  linarith

open scoped Classical in
/-- An endomorphism Y of K × Kⁿ that preserves both factors and acts by ν on the first is ν ⊕ N, and
the characteristic roots of N are those of Y with one copy of ν removed. -/
lemma exists_charpoly_roots_eq_erase [DecidableEq n]
    {K : Type*} [Field K] (ν : K) (Y : Module.End K (K × (n → K)))
    (hY_first : Y (1, 0) = (ν, 0)) (hY_second : ∀ w : n → K, (Y (0, w)).1 = 0) :
    ∃ N : Matrix n n K,
      (∀ x : K × (n → K), Y x = (ν * x.fst, N *ᵥ x.snd)) ∧
        N.charpoly.roots = Y.charpoly.roots.erase ν := by
  let N : Matrix n n K := (snd K K (n → K) ∘ₗ Y ∘ₗ inr K K (n → K)).toMatrix'
  -- The first block `ν` is written `0 - -ν • 1` so that `charpoly_sub_smul` gives its
  -- characteristic polynomial `X - C ν`.
  have Y_eq : Y = .prodMap (0 - -ν • 1) N.toLin' := by
    ext <;> simp [N, hY_first, hY_second, Prod.mk_zero_zero]
  have charpoly_eq : Y.charpoly = (X - C ν) * N.charpoly := by
    rw [Y_eq, charpoly_prodMap, charpoly_sub_smul]
    simp [sub_eq_add_neg]
  refine ⟨N, fun x ↦ by simp [Y_eq], ?_⟩
  simp [charpoly_eq, roots_mul (mul_ne_zero (X_sub_C_ne_zero ν) N.charpoly_monic.ne_zero)]

/-- The point of an analytic family f at p = (b, z): it has the frame of f, the reflection of the
member b, and the vectors Q_b⁻¹(z_i) + P_i, where Q_b is the period map of the member b. -/
@[simp]
def AnalyticFamily.ballPoint {ν : ℕ} (f : AnalyticFamily D) (P : Fin ν → RealVectors E D.Index)
    (p : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
    ModuliPoint E D.Index ν :=
  ModuliPoint.mk f.frame (f.reflection p.1) ((f.torus p.1).realEquiv.symm ∘ p.2 + P)
    ⟨(f.torus p.1).formMatrix, (f.torus p.1).isSignedFrameFor⟩ (f.torus p.1).reflection

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- The Hecke translate of an analytic family by a similitude γ: it has the frame gγ, the same
domain, reflections and period maps, and the matrix β and each form B are multiplied by the positive
rational c with γᴴ(c·1)γ a unit of Ẑ, that is, by the inverse of the rational similitude factor of
γ. -/
def AnalyticFamily.heckeTranslate (f : AnalyticFamily D) (γ : GUPlus E D.Index) :
    AnalyticFamily D := by
  -- `c > 0` is the inverse of the rational multiplier of the similitude `γ`: `γᴴ (c • 1) γ` is a
  -- unit of `Ẑ`
  have h_similitude : ∃ c : ℚ, 0 < c ∧ IsFrameFor ((c : E) • 1) γ.val :=
    (mem_GUPlus_iff.1 γ.prop).left
  choose c hc hγ using h_similitude
  exact
    { domain := f.domain
      isConnected := f.isConnected
      frame := f.frame * γ
      reflection := f.reflection
      torus b :=
        let x : ThetaTori.ThetaTorus D f.frame (f.reflection b) (BallFibre E D.Index) :=
          f.torus b
        { formMatrix := (c : E) • x.formMatrix
          realEquiv := x.realEquiv
          automorphyForm := c • x.automorphyForm
          isFrameFor := x.isFrameFor.mul_iff.2 hγ
          isPeriodMap := x.isPeriodMap
          re_symm := by simp [x.re_symm]
          riemannForm_eq := by
            simp [map_rat_smul, x.riemannForm_eq, Rat.smul_def, mul_left_comm, polarisationForm,
              PEL.xi_im_pos_and_re_eq_zero, mul_sum, map_smul', smul_mulVec]
          isPosRiemann := isPosRiemann_of_re_pos (by simpa [hc, Prod.ext_iff] using f.re_pos b)
          reflection := x.reflection
          adjoint := by simpa [hc.ne', ThetaTori.PeriodMap.intAction] using x.adjoint
          exists_std_equiv := x.exists_std_equiv }
      analyticAt := f.analyticAt
      eq_zero_of_linear := f.eq_zero_of_linear
      form_const := by simp [f.form_const 0]
      re_pos := by simpa [hc, Prod.ext_iff] using f.re_pos }

/-- Let `f` be an analytic family whose frame `f.frame` has the sign condition for the matrix `β`
and some complex matrix `ℓ` (only `β` is used afterwards) (`hβ`), let `H = Φ_{v₀}(β)` be negative
definite on the vectors `y ≠ 0` with `(e (star y)).fst = 0` (`hneg`), let the domain of `f` be
`positiveBall e H` (`hU`), and let its reflection at `b` be the reflection for `H` in
`star (e.symm (1, b))` (`hℓ`). Then every moduli point `a` with frame `f.frame` is the point
`f.ballPoint 0 p` for some `p` whose first coordinate lies in the domain. -/
lemma AnalyticFamily.exists_ballPoint_eq {ν : ℕ} (f : AnalyticFamily D)
    (e : (D.Index → ℂ) ≃L[ℂ] ℂ × BallBase D.Index) {ℓ : Matrix D.Index D.Index ℂ}
    {β : Matrix D.Index D.Index E} (hβ : IsSignedFrameFor f.frame ℓ β)
    (hneg : ∀ y ≠ (0 : D.Index → ℂ), (e (star y)).fst = 0 → star y ⬝ᵥ β.map (Φ v₀) *ᵥ y < 0)
    (hU : f.domain.carrier = positiveBall e (β.map (Φ v₀)))
    (hℓ : ∀ b ∈ f.domain, f.reflection b = formReflection (β.map (Φ v₀)) (star (e.symm (1, b))))
    (a : ModuliPoint E D.Index ν) (ha : a.frame = f.frame) :
    ∃ p ∈ f.domain.carrier ×ˢ .univ, f.ballPoint 0 p = a := by
  -- The point has the same form `β`; its involution is the reflection in a positive vector `u`,
  -- and `e (star u)` scales to some `(1, b)`.
  obtain ⟨x, J, P, ⟨β', hβ'⟩, hJ⟩ := a
  cases ha
  obtain rfl : β = β' := by simpa using hβ'.conjTranspose_mul_mul_eq_smul hβ (y := 1)
                              ⟨one_pos, 1, by simp⟩
  have hdef : (β.map (Φ v₀) * J).PosDef := by simpa using hβ'.right v₀
  obtain ⟨u, hu, rfl⟩ := exists_eq_formReflection hβ.left.isHermitian_map hdef hJ
  have hu_ne_zero : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hu_ne : (e (star u)).fst ≠ 0 := mt (hneg u hu_ne_zero) hu.not_gt
  obtain ⟨b, hb⟩ : ∃ b : BallBase D.Index, (1, b) = (e (star u)).fst⁻¹ • e (star u) := by
    simp [hu_ne, Prod.ext_iff]
  have hb_ball : b ∈ positiveBall e (β.map (Φ v₀)) := by
    simpa [hb, hu_ne, inv_mul_eq_div, div_div, mul_conj, mulVec_smul] using (Complex.lt_def.1 hu).1
  have hbU : b ∈ f.domain := hU.ge hb_ball
  refine ⟨(b, (f.torus b).realEquiv ∘ P), ?_⟩
  -- Scaling `u` does not change the reflection.
  have hu_conj : starRingEnd ℂ (e (star u)).fst ≠ 0 := by simpa using hu_ne
  simp [hℓ b hbU, hbU, hb, formReflection, ext_iff_mulVec, funext_iff, field, mulVec_smul,
    smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]

/-- The action on the fibre (ℂ × ℂ^(n−1)) × ∏_{v ≠ v₀} ℂⁿ = `New.Variety.BallFibre` that matches a •
z on periods, for z in GL_n(E) with eigenvalue μ at v₀, the block `N` of its entrywise conjugate in
the ball chart and a in E: multiplication by Φ_{v₀}(a)μ, by the conjugate of Φ_{v₀}(a) times `N`,
and by Φ_v(a)Φ_v(z) at each place v ≠ v₀. -/
private def fibreEnd (μ : ℂ) (N : Matrix (Fin (card D.Index - 1)) (Fin (card D.Index - 1)) ℂ)
    (z : GL D.Index E) (a : E) : Module.End ℂ (BallFibre E D.Index) :=
  ((mulLeft ℂ (Φ v₀ a * μ)).prodMap (star (Φ v₀ a) • N).toLin').prodMap
    (piMap fun v : {v // v ≠ v₀} ↦ (Φ v.val a • z.val.map (Φ v.val)).toLin')

/-- The linear map on the coordinates (b, (z_i)_i) of points near the base point of a ball family
that an isomorphism z with eigenvalue μ and block `N` induces: (μ̄)⁻¹N on b, and
`New.Variety.fibreEnd` at α i on z_i. -/
private def ballEnd {ν : ℕ} (μ : ℂ)
    (N : Matrix (Fin (card D.Index - 1)) (Fin (card D.Index - 1)) ℂ) (z : GL D.Index E)
    (α : Fin ν → NumberField.RingOfIntegers E) :
    Module.End ℂ (BallBase D.Index × (Fin ν → BallFibre E D.Index)) :=
  (star μ⁻¹ • N).toLin'.prodMap (piMap fun i : Fin ν ↦ fibreEnd μ N z (α i))

/-- The map 1 − t·`ballEnd μ N z α` is block diagonal, so its determinant is the product of the
factors 1 − tλ over the eigenvalues λ of its blocks: (μ̄)⁻¹ times the roots of `N`; and for each i,
Φ_{v₀}(α i)μ, the conjugate of Φ_{v₀}(α i) times the roots of `N`, and Φ_v(α i) times the roots of
the characteristic polynomial of z at each place v ≠ v₀. -/
private lemma det_one_sub_smul_ballEnd {ν : ℕ} (μ : ℂ)
    (N : Matrix (Fin (card D.Index - 1)) (Fin (card D.Index - 1)) ℂ) (z : GL D.Index E)
    (α : Fin ν → NumberField.RingOfIntegers E) (t : ℂ) :
    LinearMap.det (1 - t • ballEnd μ N z α) =
      (N.charpoly.roots.map fun r : ℂ ↦ 1 - t * star μ⁻¹ * r).prod *
        ∏ i : Fin ν, (1 - t * (Φ v₀ (α i : E) * μ)) *
          (N.charpoly.roots.map fun r : ℂ ↦ 1 - t * star (Φ v₀ (α i : E)) * r).prod *
          ∏ v : {v // v ≠ v₀},
            ((z.val.charpoly.map (Φ v)).roots.map
              fun r : ℂ ↦ 1 - t * Φ v.val (α i : E) * r).prod := by
  have h_block : 1 - t • ballEnd μ N z α =
      .prodMap (1 - t • (star μ⁻¹ • N).toLin') (piMap fun i : Fin ν ↦
        .prodMap (.prodMap (1 - t • mulLeft ℂ (Φ v₀ (α i : E) * μ))
            (1 - t • (star (Φ v₀ (α i : E)) • N).toLin'))
          (piMap fun v : {v // v ≠ v₀} ↦
            1 - t • (Φ v.val (α i : E) • z.val.map (Φ v.val)).toLin')) := rfl
  simp [h_block, det_prodMap, det_pi, piMap, ← det_toMatrix', map_smul,
    det_one_sub_smul_eq_prod_roots, charpoly_map, prod_mul_distrib, smul_smul]

/-- Let μ be the j-th root (`New.Variety.numberedRoots`) under Φ_{v₀} of the separable
characteristic polynomial P of z, let every root r of P under Φ_{v₀} have r·r̄ = μ·μ̄, and let the
roots of `N` be those of P under the conjugate of Φ_{v₀} with one copy of μ̄ removed. Then the
polynomial p = `New.Variety.localTerm` α P j satisfies p(t) = p(0)·det(1 − t·`ballEnd μ N z α`). -/
private lemma eval_localTerm_eq_mul_det {ν : ℕ} {z : GL D.Index E} {j : D.Index}
    {α : Fin ν → NumberField.RingOfIntegers E} {μ : ℂ}
    {N : Matrix (Fin (card D.Index - 1)) (Fin (card D.Index - 1)) ℂ}
    (hz : z.val.charpoly.Separable) (hμ : μ = numberedRoots (Φ v₀) z.val.charpoly j) (hμ_ne : μ ≠ 0)
    (hnorm : ∀ r ∈ (z.val.charpoly.map (Φ v₀)).roots, r * star r = μ * star μ)
    (hN_roots : N.charpoly.roots = (z.val.charpoly.map (star (Φ v₀))).roots.erase (star μ))
    (t : ℂ) :
    (localTerm α z.val.charpoly j).eval t =
      (localTerm α z.val.charpoly j).eval 0 * LinearMap.det (1 - t • ballEnd μ N z α) := by
  -- As `μ * star μ = r * star r`, a factor `μ * t - r` of the Lagrange polynomial is its value
  -- at `t = 0` times a factor of `det (1 - t • (star μ)⁻¹ • N)`.
  have hfactor (r : ℂ) (hr : r ∈ (z.val.charpoly.map (Φ v₀)).roots) :
      μ * t - r = -r * (1 - (star μ)⁻¹ * star r * t) := by
    grind [hnorm r hr, star_ne_zero.2 hμ_ne]
  subst hμ
  -- Split the embeddings into the `Φ v` and their conjugates, `v₀` apart, and the roots at `v₀`
  -- into `μ` and the others; the factors of `lieRoots` without `X` do not depend on `t`.
  simp [det_one_sub_smul_ballEnd, hN_roots, hfactor, hz, localTerm, lieRoots, IsLieRoot,
    Lagrange.basis, Lagrange.basisDivisor, eval_prod, ↓prod_embeddings_eq_prod_pairs,
    prod_eq_mul_prod_subtype_ne _ v₀, @Subtype.prop _ (· ≠ _), ↓roots_map_conjugate, ← map_val,
    ← map_erase, ← Multiset.map_erase _ star_injective, ← erase_val, prod_ite, filter_eq',
    filter_ne', sub_ite, ← star_def, mul_comm t, mul_assoc, prod_mul_distrib,
    -mul_eq_mul_left_iff, -neg_mul, -RCLike.star_def, roots_eq_map_numberedRoots]
  ring

/-- An analytic family f around the point o, with A p = `f.ballPoint o.markedPoint p` its point at p
with the vectors of o: A 0 = o, f meets every point with the frame of o, and an isomorphism from a
translate of o to o acts linearly on the parameters near 0, with a determinant formula for its local
term. -/
structure IsBallFamily {ν : ℕ} (o : ModuliPoint E D.Index ν) (f : AnalyticFamily D) : Prop where
  /-- The domain of the family contains the parameter `0`. -/
  zero_mem : 0 ∈ f.domain
  /-- At `0` the family passes through `o`. -/
  ballPoint_zero : f.ballPoint o.markedPoint 0 = o
  /-- Each point with the frame of `o` is the point of `f` at some p with p.1 ∈ f.domain and vectors
  0. -/
  exists_ballPoint_eq (a : ModuliPoint E D.Index ν) (ha : a.frame = o.frame) :
    ∃ p ∈ f.domain.carrier ×ˢ .univ, f.ballPoint 0 p = a
  /-- If z : o·(g, α) ≅ o at level `levelGU D.Index D.level` has separable characteristic polynomial
  and the reflection of o is `markedReflection z j`, some linear map K has z : A(q)·(g, α) ≅ A(Kq)
  for q near 0, where A(q) = `f.ballPoint o.markedPoint q`, and p(t) = p(0)·det(1 − tK) for
  p = `localTerm α z.val.charpoly j`. -/
  exists_linear_isLevelIso {g : GUPlus E D.Index} {α : Fin ν → NumberField.RingOfIntegers E}
    {z : GL D.Index E} {j : D.Index} (hz : z.val.charpoly.Separable)
    (h_refl : o.reflection = markedReflection z j)
    (h_iso : (o.act g α).IsLevelIso (levelGU D.Index D.level) z o) :
    ∃ K : Module.End ℂ (BallBase D.Index × (Fin ν → BallFibre E D.Index)),
      (∀ᶠ q in 𝓝 0, ((f.ballPoint o.markedPoint q).act g α).IsLevelIso (levelGU D.Index D.level) z
        (f.ballPoint o.markedPoint (K q))) ∧
      ∀ t : ℂ, (localTerm α z.val.charpoly j).eval t = (localTerm α z.val.charpoly j).eval 0 *
        (1 - t • K).det

/-- Every moduli point `o` (a finite adelic frame, a reflection `J` and marked vectors) has a ball
family: an analytic family of theta tori `f` whose point at parameter 0, with the marked vectors of
`o`, is `o`. The family passes through every moduli point having the same frame as `o`, and an
isomorphism from a translate of `o` to `o` acts linearly on its parameters near 0
(`New.Variety.IsBallFamily`). -/
theorem exists_isBallFamily {ν : ℕ} (o : ModuliPoint E D.Index ν) :
    ∃ f : AnalyticFamily D, IsBallFamily o f := by
  -- Let `β` be the form of the frame of `o`; the involution `o.reflection` is the reflection in a
  -- positive vector `u₀`. Positive lines form a ball, which carries the family of
  -- `exists_analyticFamily_positiveBall`. An automorphism `z` preserves the line of `u₀`, so it
  -- acts linearly on the coordinates of the ball and on the periods.
  obtain ⟨x₀, J₀, P₀, ⟨β, hsig⟩, hJ₀⟩ := o
  have hH : (β.map (Φ v₀)).IsHermitian := hsig.left.isHermitian_map
  have hdef : (β.map (Φ v₀) * J₀).PosDef := by simpa using hsig.right v₀
  obtain ⟨u₀, hu₀, rfl⟩ := exists_eq_formReflection hH hdef hJ₀
  obtain ⟨e, hstar, he, he₀⟩ := exists_ball_chart hH rfl hu₀
  have h0 : 0 ∈ positiveBall e (β.map (Φ v₀)) := by simpa [he₀] using (Complex.lt_def.1 hu₀).1
  -- The form is negative definite on the orthogonal complement of `u₀`, where `J₀ = -1`.
  have hneg (y : D.Index → ℂ) (hy : y ≠ 0) (hy_first : (e (star y)).fst = 0) :
      star y ⬝ᵥ β.map (Φ v₀) *ᵥ y < 0 := by
    simpa [← he (star y), hy_first, sub_mulVec, mulVec_smul, smul_mulVec, ← mulVec_mulVec,
      vecMulVec_mulVec, mulVec_sub] using hdef.dotProduct_mulVec_pos (x := y) hy
  obtain ⟨f, hU, rfl, hf⟩ :=
    exists_analyticFamily_positiveBall e (hstar.isPathConnected h0).isConnected hneg hsig rfl
  replace h0 : 0 ∈ f.domain := hU.ge h0
  refine ⟨f, h0, by simp [hf _ h0, he₀],
    f.exists_ballPoint_eq e hsig hneg hU fun b hb ↦ (hf b hb).left,
    fun {g α z j} hz h_refl h_iso ↦ ?_⟩
  -- The automorphism `z` is a similitude of `β`, `zᴴ β z = c • β` (`hsim`), and all its
  -- eigenvalues at all places have square norm `c` (`hnorm`).
  obtain ⟨c, hc⟩ := div_mem g.property.left h_iso.mem_level.left
  have h_frame : IsScalarFrame (f.frame⁻¹ * toFinGL z * f.frame)⁻¹ c := by
    simpa [← mul_assoc, ModuliPoint.act] using hc
  obtain ⟨hsim, hnorm⟩ := hsig.similitude_and_root_norm h_frame h_iso.reflection_eq
  -- `u₀` is an eigenvector of `z` at `v₀`, for the root `μ` with index `j`.
  obtain ⟨i, heig, hi⟩ := (isReflection_markedReflection_and_exists_eq_iff hz).2 _ hJ₀
    h_iso.reflection_eq
  obtain rfl : j = i := ((hi j).1 h_refl).symm
  set μ : ℂ := numberedRoots (Ψ.Φ v₀) z.val.charpoly j
  have hμ : z.val.map (Φ v₀) *ᵥ u₀ = μ • u₀ := by
    simpa [hu₀.ne', smul_comm μ, mulVec_smul, smul_mulVec, -vecMulVec_smul, ← mulVec_mulVec,
      vecMulVec_mulVec, ← dotProduct_mulVec] using
      congrArg (fun M : Matrix D.Index D.Index ℂ ↦ M *ᵥ u₀) heig
  have hμ_norm : μ * star μ = c := hnorm v₀ μ (by simp [μ, roots_eq_map_numberedRoots hz])
  have hc_ne : (c : ℂ) ≠ 0 := by aesop
  have hμ_ne : μ ≠ 0 := left_ne_zero_of_mul (hμ_norm.trans_ne hc_ne)
  have hform (x w : D.Index → ℂ) :
      x ᵥ* (z.val.map (Φ v₀))ᴴ ⬝ᵥ β.map (Φ v₀) *ᵥ z.val.map (Φ v₀) *ᵥ w =
        c * x ⬝ᵥ β.map (Φ v₀) *ᵥ w := by
    simpa [↓map_conjTranspose_mul_mul, dotProduct_mulVec _ _ᴴ, smul_mulVec, ← mulVec_mulVec,
      map_smul'] using congrArg (fun M : Matrix D.Index D.Index E ↦ x ⬝ᵥ M.map (Φ v₀) *ᵥ w) hsim
  -- In the chart `e` the complex conjugate of `z` preserves both factors (the second by `hform`),
  -- so it is `star μ ⊕ N`; the eigenvalues of `N` are the conjugates of the other roots.
  have h_first : e.conj (z.val.map (Φ v₀))ᴴᵀ.toLin' (1, 0) = (star μ, 0) := by
    simp [hμ, he₀, ← star_mulVec, ← e.symm_apply_eq.1 he₀, mulVec_transpose]
  have h_second (w : BallBase D.Index) : (e.conj (z.val.map (Φ v₀))ᴴᵀ.toLin' (0, w)).fst = 0 := by
    simpa [hμ, ← he (_ ᵥ* _), ← he (e.symm _), hu₀.ne', hμ_ne, mulVec_smul, mulVec_transpose] using
      hform (e.symm (0, w)) u₀
  obtain ⟨N, hN, hN_roots⟩ := exists_charpoly_roots_eq_erase (star μ) _ h_first h_second
  -- `erw`: `ᴴᵀ` is the entrywise conjugate only after unfolding, which `rw` does not do.
  have h_roots : N.charpoly.roots = (z.val.charpoly.map (star (Φ v₀))).roots.erase (star μ) := by
    erw [hN_roots, e.charpoly_conj, charpoly_toLin', z.val.charpoly_map (star _)]
  -- `fibreEnd μ N z a` is the action of `a • z` on periods; `ballEnd μ N z α` moves the base
  -- point by `(star μ)⁻¹ • N`.
  refine ⟨ballEnd μ N z α, ?_, eval_localTerm_eq_mul_det hz rfl hμ_ne
    (fun r hr ↦ (hnorm v₀ r hr).trans hμ_norm.symm) h_roots⟩
  have hnear : ∀ᶠ p in 𝓝 0, (ballEnd μ N z α p).fst ∈ f.domain ∧ p.fst ∈ f.domain :=
    ((f.domain.isOpen.prod f.domain.isOpen).preimage (f := fun p ↦ ((ballEnd μ N z α p).fst, p.fst))
      (by fun_prop)).mem_nhds (by simpa)
  filter_upwards [hnear] with p ⟨hKp, hp⟩
  -- The periods intertwine `a • z` and `fibreEnd μ N z a`: in the first coordinate this is
  -- `hform`.
  have h_Q_smul (a : E) (w : RealVectors E D.Index) :
      (f.torus (ballEnd μ N z α p).fst).realEquiv (cmEmbedding a • z.val.map cmEmbedding *ᵥ w) =
        fibreEnd μ N z a ((f.torus p.fst).realEquiv w) := by
    have hconj (y : D.Index → ℂ) :
        y ᵥ* (z.val.map (Φ v₀))ᴴ = e.symm (star μ * (e y).fst, N *ᵥ (e y).snd) := by
      simpa [← e.eq_symm_apply, mulVec_transpose] using hN (e y)
    simp [hf _ hp, hf _ hKp, mulVec_smul, -smul_eq_mul, ← Pi.smul_def, smul_smul, Prod.ext_iff,
      -mulVec_mulVec]
    simpa [fibreEnd, ballEnd, star_mulVec, hconj, funext_iff, hμ_ne, ← hμ_norm, field,
      mulVec_smul, mulVec_sub] using Or.inl (hform (star μ⁻¹ • e.symm (1, p.fst)) _)
  -- `IsPeriodMap.ratConj_eq`: a complex linear map of periods induced by `z` makes `z` conjugate
  -- the reflections
  refine ⟨h_iso.mem_level, (f.torus _).isPeriodMap.ratConj_eq (f.torus _).isPeriodMap
    (fibreEnd μ N z 1) (by simp [← h_Q_smul]), ?_⟩
  simpa [ballEnd, (f.torus _).realEquiv.eq_symm_apply.2 (h_Q_smul ..), mulVec_smul, mulVec_add,
    ModuliPoint.act] using h_iso.sub_mem_lattice

end New.Variety

end BallModel

end
