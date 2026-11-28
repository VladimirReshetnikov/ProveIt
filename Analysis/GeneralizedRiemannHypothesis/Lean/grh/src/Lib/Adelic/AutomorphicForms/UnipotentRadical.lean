import Lib.Adelic.AutomorphicForms.RealConvolution
import Lib.DiscreteSeries.CuspKernel

/-!
# The mean along a unipotent radical vanishes; reduction in the radical

This file defines the adelic unipotent radical `New.unipotentRadical` of the stabiliser of the
span of the columns of an isotropic adelic matrix. A bounded continuous function that is fixed by
right convolution with a cusp kernel `e` (`New.IsCuspKernel`) and invariant under the rational
points of the radical, of finite covolume, has mean zero along the radical. From this it derives a
bound by the oscillation for such functions. It also gives the matrix algebra for the reduction
step, `New.Reduction.radicalElem` and `New.Reduction.IsIntBounded`, which moves an adelic point of a
unipotent radical close to `1` by a rational element.

## Main definitions and results

* `New.Space.integral_unipotentRadical_eq_zero`: the mean along the radical vanishes.
* `New.unipotentRadical`: the points `g` of the adelic unitary group that fix the span `A` of the
  columns of `a` pointwise and satisfy `uᴴ J (g v) = uᴴ J v` for all `u`, `v` in `A^⊥`, where
  `J = stdForm E s`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places (in the coordinates x⁻¹ X this
  form is the adelic matrix `stdForm E s`); `V.Γ` is its group of rational points in the adelic
  group G = G_∞ × G_f, and `V.move g` has the point xg.
* `New.realConv`: R(k)F(g) = ∫ k(x) F(gx) dx over G_∞ (`New.GInf`, one copy of U(diag s) for each
  infinite place of E), for k on G_∞ and F on G.
* `New.IsCuspKernel`: a minimal idempotent for convolution on G_∞ that decays polynomially and is
  reproduced by a compactly supported function.
* `New.dilationGroup a`: the pairs (g, c) such that g is the scalar c on the columns of a and
  wᴴ J (g v) = wᴴ J v for all v, w orthogonal to these columns.

## Relation to the literature

Known; see `Lib.Adelic.AutomorphicForms.Cuspidality` for sources.
-/

/-! ## The mean along a unipotent radical vanishes -/

section Cuspidal

open Subgroup MeasureTheory Matrix Real Set Norms.L2Operator Metric NumberField

namespace New

/-- An element `x` of the unitary group of `J` is a dilation along `A` by the factor `1` if and only
if it fixes `A` and `wᴴ J x v = wᴴ J v` for all `v`, `w` orthogonal to `A`. -/
theorem mk_one_mem_dilationGroup_iff {n m R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [StarRing R] {J : Matrix n n R} {A : Matrix n m R} {x : U J} :
    (x, 1) ∈ dilationGroup A ↔ (x : Matrix n n R) * A = A ∧
      ∀ v w : Matrix n n R, Aᴴ * (J * v) = 0 → Aᴴ * (J * w) = 0 →
        wᴴ * (J * (x * v)) = wᴴ * (J * v) := by
  change (x : Matrix n n R) * A = (1 : Rˣ) • A ∧ _ ↔ _
  exact and_congr_left' (by rw [one_smul])

/-- The points `g` of the adelic unitary group that fix the span `A` of the columns of `a` pointwise
and satisfy `uᴴ J (g v) = uᴴ J v` for all `u`, `v` in `A^⊥`, where `J = stdForm E s`. For isotropic
`A` with `A^⊥⊥ = A` these are the points that fix `A` and `A^⊥ / A` pointwise: the unipotent radical
of the stabiliser of `A`. -/
noncomputable def unipotentRadical {E n : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n]
    (s : n → ℤˣ) (a : Matrix n n (𝔸 E)) : Subgroup (G E s) :=
  (dilationGroup (m := n) a).comap (G.toUnitary.toMonoidHom.prod 1)

section Radical

/-- The pairing `xᴴ (stdForm E s) y` of two adelic matrices, read at an infinite place `w`, is the
pairing of their components at `w` for the diagonal matrix of the signs `s`. -/
theorem conjTranspose_map_evalInf_mul_signMatrix_mul {E n : Type*} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] (w : InfinitePlace E) (x y : Matrix n n (𝔸 E)) :
    (x.map (evalInf w))ᴴ * (signMatrix s * y.map (evalInf w)) =
      (xᴴ * (stdForm E s * y)).map (evalInf w) := by
  have h_form : (stdForm E s).map (evalInf w) = signMatrix s := by simp [stdForm, signMatrix]
  have h_star : xᴴ.map (evalInf w) = (x.map (evalInf w))ᴴ := rfl
  rw [Matrix.map_mul, Matrix.map_mul, h_form, h_star]

variable {E n : Type*} {s : n → ℤˣ} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {a : Matrix n n (𝔸 E)}

/-- A point `g` lies in the radical of `a` if and only if it fixes `a` and `uᴴ J g v = uᴴ J v` for
all `v`, `u` orthogonal to `a`, where `J` is the standard form. -/
theorem mem_unipotentRadical_iff {g : G E s} :
    g ∈ unipotentRadical s a ↔ g.adeleMatrix * a = a ∧
      ∀ v u : Matrix n n (𝔸 E), aᴴ * (stdForm E s * v) = 0 → aᴴ * (stdForm E s * u) = 0 →
        uᴴ * (stdForm E s * (g.adeleMatrix * v)) = uᴴ * (stdForm E s * v) :=
  mk_one_mem_dilationGroup_iff (x := g.toUnitary)

/-- The radical is closed in the adelic unitary group. -/
instance isClosed_unipotentRadical (a : Matrix n n (𝔸 E)) :
    IsClosed (unipotentRadical s a : Set (G E s)) := by
  -- It is an intersection of solution sets of equations between continuous functions.
  rw [← SetLike.setOfPred_mem_eq (unipotentRadical s a)]
  simp only [mem_unipotentRadical_iff, ofPred_and, ofPred_forall]
  exact (isClosed_eq (by fun_prop) continuous_const).inter <| isClosed_iInter fun v ↦
    isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const

/-- If at every infinite place `w` the component `r w` of a real point `r` is a dilation by the
factor `1` along the component of `a`, then `(r, 1)` lies in the adelic radical of `a`. -/
theorem mk_one_mem_unipotentRadical {r : GInf E s}
    (hr : ∀ w : InfinitePlace E, (r w, 1) ∈ dilationGroup (m := n) (a.map (evalInf w))) :
    ((r, 1) : G E s) ∈ unipotentRadical s a := by
  -- Both equations are trivial at the finite places and are those of `hr` at the infinite ones.
  have h_inf (w : InfinitePlace E) (v : Matrix n n (𝔸 E)) :
      (G.adeleMatrix ((r, 1) : G E s) * v).map (evalInf w) = (r w : Matrix n n ℂ) * v.map
        (evalInf w) :=
    Matrix.map_mul
  have h_fin (v : Matrix n n (𝔸 E)) :
      (G.adeleMatrix ((r, 1) : G E s) * v).map (RingHom.snd _ (𝔸f E)) = v.map
        (RingHom.snd _ (𝔸f E)) :=
    Matrix.map_mul.trans (one_mul _)
  choose h_fixes h_trivial using fun w ↦ mk_one_mem_dilationGroup_iff.1 (hr w)
  refine mem_unipotentRadical_iff.2 ⟨matrix_ext_𝔸 (fun w ↦ ?_) (h_fin a),
    fun v u hv hu ↦ matrix_ext_𝔸 (fun w ↦ ?_) ?_⟩
  · rw [h_inf, h_fixes]
  · rw [← conjTranspose_map_evalInf_mul_signMatrix_mul,
    ← conjTranspose_map_evalInf_mul_signMatrix_mul, h_inf]
    exact h_trivial w _ _ (by simp [conjTranspose_map_evalInf_mul_signMatrix_mul, hv])
      (by simp [conjTranspose_map_evalInf_mul_signMatrix_mul, hu])
  · rw [Matrix.map_mul, Matrix.map_mul, h_fin, ← Matrix.map_mul, ← Matrix.map_mul]

end Radical

section Height

variable {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {A : Matrix n n ℂ}

theorem coe_uSign_mul_ne_zero (hA : A ≠ 0) (z : USign s) : (z : Matrix n n ℂ) * A ≠ 0 :=
  mt (z : GL n ℂ).mul_right_eq_zero.1 hA

/-- For a matrix `A ≠ 0`, the function `x ↦ log ‖x⁻¹ A‖` on the unitary group of signature `s`
changes by at most `‖y‖` under right translation by `y` (operator norms). -/
theorem abs_log_norm_inv_mul_sub_le (hA : A ≠ 0) (x y : USign s) :
    |log ‖(((x * y)⁻¹ : USign s) : Matrix n n ℂ) * A‖ -
      log ‖((x⁻¹ : USign s) : Matrix n n ℂ) * A‖| ≤ ‖(y : Matrix n n ℂ)‖ := by
  let N (z : USign s) : ℝ := ‖((z⁻¹ : USign s) : Matrix n n ℂ) * A‖
  have N_pos (z : USign s) : 0 < N z := norm_pos_iff.2 (coe_uSign_mul_ne_zero hA z⁻¹)
  have h_step (x y : USign s) :
      log (N (x * y)) - log (N x) ≤ ‖((y⁻¹ : USign s) : Matrix n n ℂ)‖ :=
    -- The logarithm of the ratio of the two norms is at most the ratio, which is at most ‖y⁻¹‖.
    calc _ = log (N (x * y) / N x) := (log_div (N_pos _).ne' (N_pos _).ne').symm
      _ ≤ N (x * y) / N x := log_le_self (by positivity)
      _ ≤ ‖((y⁻¹ : USign s) : Matrix n n ℂ)‖ := by
        rw [div_le_iff₀ (N_pos x)]
        simp only [N, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, mul_assoc, norm_mul_le]
  refine abs_sub_le_iff.2 ⟨(h_step x y).trans_eq (U.norm_inv y), ?_⟩
  simpa only [mul_inv_cancel_right, inv_inv] using h_step (x * y) y⁻¹

/-- If `r ∈ U(diag s)` dilates the non-zero matrix `A` by the factor `c` (in particular
`r A = c A`), left translation by `r` lowers `log ‖x⁻¹ A‖` by `log ‖c‖`. -/
theorem log_norm_inv_mul_of_mem_dilationGroup (hA : A ≠ 0) {r : USign s} {c : ℂˣ}
    (hr : (r, c) ∈ dilationGroup (m := n) A) (x : USign s) :
    log ‖(((r * x)⁻¹ : USign s) : Matrix n n ℂ) * A‖ =
      -log ‖(c : ℂ)‖ + log ‖((x⁻¹ : USign s) : Matrix n n ℂ) * A‖ := by
  have h_inv : ((r⁻¹ : USign s) : Matrix n n ℂ) * A = ((c⁻¹ : ℂˣ) : ℂ) • A := (inv_mem hr).1
  have h_scale : (((r * x)⁻¹ : USign s) : Matrix n n ℂ) * A =
      ((c⁻¹ : ℂˣ) : ℂ) • (((x⁻¹ : USign s) : Matrix n n ℂ) * A) := by
    rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, mul_assoc, h_inv, Matrix.mul_smul]
  rw [h_scale, norm_smul, Units.val_inv_eq_inv_val, norm_inv,
    log_mul (by simp) (norm_ne_zero_iff.2 (coe_uSign_mul_ne_zero hA x⁻¹)), log_inv]

end Height

/-- For E a CM field, let `GInf E s` be the product of the unitary groups U(diag s) over the
infinite places, and `A` a family of non-zero matrices with (A w)ᴴ diag(s) A w = 0. A cusp kernel
`e` of order `B` is a minimal idempotent with ‖x‖^(B+1)e(x) integrable, ‖x‖^B e(x) bounded and α ∗
e = e for some compactly supported continuous α. It annihilates every bounded continuous `Ψ` that is
left invariant under each `r` whose components `r w` fix the columns of `A w` and satisfy vᴴ diag(s)
(r w) u = vᴴ diag(s) u for v, u orthogonal to them: `∫ e(x) Ψ(y x) dx = 0` for all `y`.

A case of Harish-Chandra's theorem that the K-finite coefficients of a discrete series have
vanishing constant terms. -/
theorem IsCuspKernel.integral_mul_eq_zero {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] [Nonempty n] {B : ℕ} {e : GInf E s → ℂ} (he : IsCuspKernel B e)
    {A : InfinitePlace E → Matrix n n ℂ}
    (hA_iso : ∀ w : InfinitePlace E, (A w)ᴴ * (signMatrix s * A w) = 0)
    (hA_ne : ∀ w : InfinitePlace E, A w ≠ 0) (Ψ : BoundedContinuousFunction (GInf E s) ℂ)
    (hΨ : ∀ r : GInf E s, (∀ w : InfinitePlace E, (r w, 1) ∈ dilationGroup (m := n) (A w)) →
      ∀ x : GInf E s, Ψ (r * x) = Ψ x)
    (y : GInf E s) : ∫ x : GInf E s, e x * Ψ (y * x) = 0 := by
  -- `P`: the pairs (r, c) such that r dilates `A` by c at every place. Under such an r the
  -- height `H`, read at one place, drops by log ‖c‖.
  let P : Subgroup (GInf E s × ℂˣ) :=
    ⨅ w : InfinitePlace E, (dilationGroup (A w)).comap (.prodMap (Pi.evalMonoidHom _ w) (.id _))
  have mem_P {r : GInf E s} {c : ℂˣ} : (r, c) ∈ P ↔ ∀ w, (r w, c) ∈ dilationGroup (A w) := mem_iInf
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  let H (x : GInf E s) : ℝ := log ‖(((x w₀)⁻¹ : USign s) : Matrix n n ℂ) * A w₀‖
  let size (x : GInf E s) : ℝ := ∏ w : InfinitePlace E, ‖(x w : Matrix n n ℂ)‖
  have H_cont : Continuous H := .log (by fun_prop) fun x ↦
    norm_ne_zero_iff.2 (coe_uSign_mul_ne_zero (hA_ne w₀) (x w₀)⁻¹)
  have H_lip (x z : GInf E s) : |H (x * z) - H x| ≤ size z ^ (B + 1) :=
    calc |H (x * z) - H x| ≤ ‖(z w₀ : Matrix n n ℂ)‖ := abs_log_norm_inv_mul_sub_le (hA_ne w₀) _ _
      _ ≤ size z := (le_prod_opNorm z).2 w₀
      _ ≤ size z ^ (B + 1) := le_self_pow₀ (le_prod_opNorm z).1 B.succ_ne_zero
  refine DiscreteSeries.integral_idempotentKernel_mul_eq_zero H (fun x ↦ size x ^ (B + 1)) P
    he.toIsIdempotentKernel he.integrable_moment H_cont H_lip (fun ⟨r, c⟩ hr x ↦ ?_)
    (fun W hW ↦ ?_) Ψ (fun r hr ↦ hΨ r (mem_P.1 hr)) y
  · exact log_norm_inv_mul_of_mem_dilationGroup (hA_ne w₀) (mem_P.1 hr w₀) (x w₀)
  · -- Dilations by 1 + δ exist in every conjugate of the ball of radius δ, place by place.
    obtain ⟨δ, hδ, hδW⟩ := nhds_basis_closedBall.mem_iff.1 hW
    have h_norm : 1 < ‖(1 + δ : ℂ)‖ := (Complex.re_le_norm _).trans_lt' (by simpa)
    let c : ℂˣ := .mk0 (1 + δ) (mod_cast by positivity)
    refine ⟨c, (log_pos h_norm).ne', fun x ↦ ?_⟩
    have h_place (w : InfinitePlace E) : ∃ z : USign s,
        dist (z : Matrix n n ℂ) 1 ≤ δ ∧ (x w * z * (x w)⁻¹, c) ∈ dilationGroup (A w) :=
      DiscreteSeries.exists_conj_mem_dilationGroup (hA_iso w) (x w) hδ
    choose z z_near z_dil using h_place
    exact ⟨z, hδW (dist_pi_le_iff'.2 z_near), mem_P.2 z_dil⟩

namespace Space

variable {E n : Type} {s : n → ℤˣ} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Nonempty n]
  (W : Space E n s) {F : G E s → ℂ} {B : ℕ} {e : GInf E s → ℂ} {a : Matrix n n (𝔸 E)} {g : G E s}
  {C : ℝ}

/-- The mean along a unipotent radical vanishes. Let `N` be the radical of an isotropic adelic
matrix `a` that vanishes at no infinite place, let `Γ` be the group of rational points of `W`, and
let `Γ ∩ N` have finite covolume in `N`. If the bounded continuous function `F` is fixed by right
convolution with a cusp kernel `e` and `F (g ·)` is left invariant under `Γ ∩ N`, the integral of
`F (g v y)` over `v ∈ (Γ ∩ N) \ N` is zero for every real `y`. Integrals over the quotient are taken
against `Subgroup.quotMeasure`, the Haar measure of `N` weighted by a cutoff for `Γ ∩ N`. -/
theorem integral_unipotentRadical_eq_zero (he : IsCuspKernel B e)
    (ha_iso : aᴴ * (stdForm E s * a) = 0) (ha_ne : ∀ w : InfinitePlace E, a.map (evalInf w) ≠ 0)
    (h_fin : IsFiniteMeasure ((W.Γ.subgroupOf (unipotentRadical s a)).quotMeasure .haar))
    (h_cont : Continuous F) (hC : ∀ x : G E s, ‖F x‖ ≤ C) (h_fix : realConv e F = F)
    (h_inv : (W.Γ ⊓ unipotentRadical s a).FixesLeft fun x : G E s ↦ F (g * x)) (y : GInf E s) :
    ∫ v : unipotentRadical s a, F (g * ((v : G E s) * (y, 1)))
      ∂(W.Γ.subgroupOf (unipotentRadical s a)).quotMeasure .haar = 0 := by
  -- The mean Ψ(x) of F(g v x) is fixed by convolution with e, since F is, and killed by it, being
  -- invariant under the real radical.
  set N : Subgroup (G E s) := unipotentRadical s a
  let ν : Measure N := (W.Γ.subgroupOf N).quotMeasure .haar
  have h_unimodular : (Measure.haar : Measure N).IsMulRightInvariant :=
    isMulRightInvariant_of_finite_covolume h_fin
  have mean_cont : Continuous fun x : GInf E s ↦ ∫ v : N, F (g * ((v : G E s) * (x, 1))) ∂ν :=
    continuous_of_dominated (by fun_prop) (fun _ ↦ .of_forall fun _ ↦ hC _) (integrable_const C)
      (.of_forall (by fun_prop))
  let Ψ : BoundedContinuousFunction (GInf E s) ℂ := .ofNormedAddCommGroup _ mean_cont
    (C * ν.real univ) fun x ↦ norm_integral_le_of_norm_le_const (.of_forall fun _ ↦ hC _)
  have hΨ (x : GInf E s) : Ψ x = ∫ v : N, F (g * ((v : G E s) * (x, 1))) ∂ν := rfl
  have h_assoc (v : G E s) (x z : GInf E s) : v * (x, 1) * (z, 1) = v * (x * z, 1) := by
    rw [mul_assoc, Prod.mk_mul_mk x, one_mul]
  -- F is fixed by convolution with e; exchange the two integrals.
  have Ψ_fix : Ψ y = ∫ x : GInf E s, e x * Ψ (y * x) :=
    calc Ψ y = ∫ v : N, 1 * realConv e F (g * ((v : G E s) * (y, 1))) ∂ν := by simp [hΨ, h_fix]
      _ = ∫ x : GInf E s, e x * ∫ v : N, 1 * F (g * ((v : G E s) * (y, 1)) * (x, 1)) ∂ν :=
          integral_mul_realConv (.of_continuous ⟨C, hC⟩ h_cont) he.integrable (integrable_const 1) _
      _ = ∫ x : GInf E s, e x * Ψ (y * x) := by simp only [hΨ, one_mul, mul_assoc g, h_assoc]
  rw [← hΨ, Ψ_fix]
  refine he.integral_mul_eq_zero (fun w ↦ ?_) ha_ne Ψ (fun r hr x ↦ ?_) y
  · simp [conjTranspose_map_evalInf_mul_signMatrix_mul, ha_iso]
  · -- (r, 1) lies in `N`, and ν is right invariant on functions invariant under the lattice.
    let u : N := ⟨(r, 1), mk_one_mem_unipotentRadical hr⟩
    have h_lattice (γ : W.Γ.subgroupOf N) (v : N) :
        F (g * (((γ • v : N) : G E s) * (x, 1))) = F (g * ((v : G E s) * (x, 1))) := by
      obtain ⟨⟨γ, hγN⟩, hγΓ⟩ := γ
      simpa [Subgroup.smul_def, mul_assoc] using h_inv γ ⟨hγΓ, hγN⟩ ((v : G E s) * (x, 1))
    calc Ψ (r * x) = ∫ v : N, F (g * (((v * u : N) : G E s) * (x, 1))) ∂ν := by
          simp only [hΨ, u, Subgroup.coe_mul, h_assoc]
      _ = Ψ x := (identDistrib_orbitMeasure_mul_right u
          (F := fun v : N ↦ F (g * ((v : G E s) * (x, 1)))) h_lattice (by fun_prop)).integral_eq

omit [Nonempty n] in
/-- Let `Γ` be the group of rational points of `W`. If the radical `N` of `a` lies in `(Γ ∩ N) K`
with `K` compact, then `Γ ∩ N` has finite covolume in `N`. -/
theorem isFiniteMeasure_quotMeasure_of_isCompact {K : Set (G E s)} (hK : IsCompact K)
    (h_cover : ∀ u ∈ unipotentRadical s a, ∃ γ ∈ W.Γ ⊓ unipotentRadical s a, γ * u ∈ K) :
    IsFiniteMeasure ((W.Γ.subgroupOf (unipotentRadical s a)).quotMeasure .haar) := by
  refine isFiniteMeasure_quotMeasure_of_cocompact (G := unipotentRadical s a) .haar
    ⟨Subtype.val ⁻¹' K, hK.preimage_val, fun u ↦ ?_⟩
  obtain ⟨γ, ⟨hγΓ, hγN⟩, hγu⟩ := h_cover u u.property
  exact ⟨⟨γ, hγN⟩, hγΓ, hγu⟩

omit [Nonempty n] in
/-- Let `Γ` be the group of rational points of `W`, and let the radical `N` of `a` lie in
`(Γ ∩ N) K` with `K` compact. If a continuous function `f`, left invariant under `Γ ∩ N`, has
integral zero over `(Γ ∩ N) \ N` and stays within `D` of a number `c` on `K`, then `‖c‖ ≤ D`. -/
theorem norm_le_of_integral_eq_zero {K : Set (G E s)} (hK : IsCompact K)
    (h_cover : ∀ u ∈ unipotentRadical s a, ∃ γ ∈ W.Γ ⊓ unipotentRadical s a, γ * u ∈ K)
    {f : G E s → ℂ} (h_cont : Continuous f) (h_inv : (W.Γ ⊓ unipotentRadical s a).FixesLeft f)
    (h_zero : ∫ v : unipotentRadical s a, f v
      ∂(W.Γ.subgroupOf (unipotentRadical s a)).quotMeasure .haar = 0)
    {c : ℂ} {D : ℝ} (hD : ∀ x ∈ K, dist (f x) c ≤ D) : ‖c‖ ≤ D := by
  -- All values of `f` on `N` are within `D` of `c`, and their mean is zero.
  set ν : Measure (unipotentRadical s a) :=
    (W.Γ.subgroupOf (unipotentRadical s a)).quotMeasure .haar
  have h_fin : IsFiniteMeasure ν := W.isFiniteMeasure_quotMeasure_of_isCompact hK h_cover
  have h_near (v : unipotentRadical s a) : f v ∈ closedBall c D := by
    obtain ⟨γ, hγ, hγv⟩ := h_cover v v.property
    simpa only [mem_closedBall, h_inv γ hγ v] using hD _ hγv
  have h_mean : ⨍ v : unipotentRadical s a, f v ∂ν ∈ closedBall c D :=
    (convex_closedBall c D).average_mem isClosed_closedBall (.of_forall h_near) <|
      .of_bound (by fun_prop) (‖c‖ + D) (.of_forall fun v ↦ norm_le_of_mem_closedBall (h_near v))
  simpa [average_eq, h_zero] using h_mean

/-- A bound by the oscillation. Let `a` be isotropic and vanish at no infinite place, and let its
radical `N` lie in `(Γ ∩ N) K`, with `Γ` the rational points of `W` and `K` compact. Let `F` be
bounded, continuous and fixed by right convolution with a cusp kernel `e`, with `F (g ·)` left
invariant under `Γ ∩ N`. If `F (g x y)` is within `D` of `F (g y)` for all `x ∈ K`, with `y` real,
then `‖F (g y)‖ ≤ D`. -/
theorem norm_le_of_dist_le (he : IsCuspKernel B e) (ha_iso : aᴴ * (stdForm E s * a) = 0)
    (ha_ne : ∀ w : InfinitePlace E, a.map (evalInf w) ≠ 0) {K : Set (G E s)} (hK : IsCompact K)
    (h_cover : ∀ u ∈ unipotentRadical s a, ∃ γ ∈ W.Γ ⊓ unipotentRadical s a, γ * u ∈ K)
    (h_cont : Continuous F) (hC : ∀ x : G E s, ‖F x‖ ≤ C) (h_fix : realConv e F = F)
    (h_inv : (W.Γ ⊓ unipotentRadical s a).FixesLeft fun x : G E s ↦ F (g * x)) (y : GInf E s)
    {D : ℝ} (hD : ∀ x ∈ K, dist (F (g * (x * (y, 1)))) (F (g * (y, 1))) ≤ D) :
    ‖F (g * (y, 1))‖ ≤ D := by
  refine W.norm_le_of_integral_eq_zero hK h_cover (f := fun x ↦ F (g * (x * (y, 1))))
    (by fun_prop) (fun γ hγ x ↦ by simpa only [mul_assoc] using h_inv γ hγ (x * (y, 1))) ?_ hD
  exact W.integral_unipotentRadical_eq_zero he ha_iso ha_ne
    (W.isFiniteMeasure_quotMeasure_of_isCompact hK h_cover) h_cont hC h_fix h_inv y

end Space

end New

end Cuspidal

/-!
## Unipotent radical elements and bounded adelic matrices

Algebra for the reduction step, which moves an adelic point of a unipotent radical close to `1` by a
rational element. The algebra is done for square matrices over a commutative ring `R` with
involution and a hermitian unit `J`.

* `New.Reduction.IsIntBounded`: adelic matrices that are integral at the finite places and of
  operator norm at most `r` at the infinite ones, with the behaviour of the bound under `star`,
  multiples, products and differences.
-/

section UnipotentReduction

open RightActions RingHom Matrix Norms.L2Operator Subgroup

namespace New.Reduction

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
  {J a y e : Matrix n n R}

/-- The matrix `1 + 2 (T - Tᴴ - Tᴴ J T) J`. If `J` is hermitian and `T = w aᴴ` with
`aᴴ J a = aᴴ J w = 0`, it is `exp (2 S) = 1 + 2 S + 2 S²` for `S = (T - Tᴴ) J`, which has `S³ = 0`;
it preserves `J`, fixes `a` and acts trivially on `a^⊥ / a`. -/
noncomputable def radicalElem (J T : Matrix n n R) : Matrix n n R :=
  1 + 2 * ((T - Tᴴ - Tᴴ * J * T) * J)

-- In this namespace `simp` unfolds `New.Reduction.radicalElem`.
attribute [scoped simp] radicalElem

/-- If `J` is hermitian and `aᴴ J w = 0`, then `aᴴ J w z = 0` and `wᴴ J a z = 0` for all `z`. -/
lemma form_mul_eq_zero (hJ : Jᴴ = J) {w : Matrix n n R} (hw : aᴴ * (J * w) = 0)
    (z : Matrix n n R) : aᴴ * (J * (w * z)) = 0 ∧ wᴴ * (J * (a * z)) = 0 := by
  have hw_adj : wᴴ * (J * a) = 0 := by simpa [hJ, mul_assoc] using congrArg conjTranspose hw
  simp [← mul_assoc, hw, hw_adj]

/-- If `J` is hermitian and `aᴴ J a = aᴴ J w = 0`, then `radicalElem J (w aᴴ)` preserves `J`. -/
lemma gram_radicalElem (hJ : Jᴴ = J) (ha : aᴴ * (J * a) = 0) {w : Matrix n n R}
    (hw : aᴴ * (J * w) = 0) : (radicalElem J (w * aᴴ))ᴴ * J * radicalElem J (w * aᴴ) = J := by
  -- Expand; the terms containing `aᴴ J a`, `aᴴ J w` or `wᴴ J a` vanish and the others cancel.
  simp [radicalElem, hJ, form_mul_eq_zero hJ ha, form_mul_eq_zero hJ hw, mul_assoc, sub_mul,
    mul_sub, two_mul, add_mul, mul_add]
  abel

/-- If `J` is hermitian and `aᴴ J a = aᴴ J w = 0`, then an element of `U J` with matrix
`radicalElem J (w aᴴ)` fixes `a` and acts trivially on `a^⊥ / a`. -/
lemma mem_dilationGroup_of_eq_radicalElem (hJ : Jᴴ = J) (ha : aᴴ * (J * a) = 0)
    {w : Matrix n n R} (hw : aᴴ * (J * w) = 0) {x : U J}
    (hx : (x : Matrix n n R) = radicalElem J (w * aᴴ)) : (x, 1) ∈ dilationGroup a := by
  have hw_adj : wᴴ * (J * a) = 0 := by simpa using (form_mul_eq_zero hJ hw 1).2
  refine mk_one_mem_dilationGroup_iff.2 ⟨?_, fun v v' hv hv' ↦ ?_⟩
  · simp [hx, ha, hw_adj, mul_assoc, sub_mul, add_mul]
  · simp [hx, hv, form_mul_eq_zero hJ hv', mul_assoc, sub_mul, two_mul, add_mul, mul_add]

/-- Let `J` be hermitian and `aᴴ J a = aᴴ J w = aᴴ J z = 0`. The product of the elements of the
radical of `a` with parameters `w` and `z` has the parameter `w + z - a wᴴ J z`. -/
lemma radicalElem_mul (hJ : Jᴴ = J) (ha : aᴴ * (J * a) = 0) {w z : Matrix n n R}
    (hw : aᴴ * (J * w) = 0) (hz : aᴴ * (J * z) = 0) :
    radicalElem J (w * aᴴ) * radicalElem J (z * aᴴ) =
      radicalElem J ((w + z - a * (wᴴ * J * z)) * aᴴ) := by
  -- Expand; the terms containing `aᴴ J a`, `aᴴ J w`, `aᴴ J z` or their adjoints vanish.
  simp [radicalElem, hJ, form_mul_eq_zero hJ ha, form_mul_eq_zero hJ hw, form_mul_eq_zero hJ hz,
    mul_assoc, sub_mul, mul_sub, two_mul, mul_add, add_mul]
  abel

/-- Let `J` be hermitian and invertible, `aᴴ J a = aᴴ J y = 0` and `y e + 2 b aᴴ J = 1`, so that the
columns of `y` span `a^⊥`. Let `u` be an element of the unitary group `U J` that fixes the columns
of `a` and satisfies `wᴴ J u v = wᴴ J v` for `v`, `w` orthogonal to `a`, so it acts trivially on
`a^⊥ / a`. Then `u = radicalElem J (y e (u - 1 - a bᴴ J u) b aᴴ)`, where
`radicalElem J T = 1 + 2 (T - Tᴴ - Tᴴ J T) J`. -/
lemma eq_radicalElem_of_mem_dilationGroup {u : U J} (hu : (u, 1) ∈ dilationGroup a)
    (hJ : Jᴴ = J) (hJ_unit : IsUnit J) {b : Matrix n n R} (ha : aᴴ * (J * a) = 0)
    (hy : aᴴ * (J * y) = 0) (h_split : y * e + 2 * b * aᴴ * J = 1) :
    (u : Matrix n n R) = radicalElem J (y * (e * (u - 1 - a * bᴴ * J * u) * b) * aᴴ) := by
  obtain ⟨hu_fixes, hu_trivial⟩ := mk_one_mem_dilationGroup_iff.1 hu
  -- The relations in the form of rewriting rules for products associated to the right.
  have ye_mul (z : Matrix n n R) : y * (e * z) = z - 2 * (b * (aᴴ * (J * z))) := by
    simpa [sub_mul, mul_assoc] using congrArg (· * z) (eq_sub_of_add_eq h_split)
  have ye_adj_mul (z : Matrix n n R) : eᴴ * (yᴴ * z) = z - 2 * (J * (a * (bᴴ * z))) := by
    simpa [hJ, two_mul, add_mul, sub_mul, mul_assoc]
      using congrArg (·ᴴ * z) (eq_sub_of_add_eq h_split)
  have preserves_mul (z : Matrix n n R) : (u : Matrix n n R)ᴴ * (J * (u * z)) = J * z := by
    rw [← mul_assoc, ← mul_assoc, show (u : Matrix n n R)ᴴ * J * u = J from u.2]
  -- `u` preserves `J` and fixes `a`, hence so does its adjoint for `J`.
  have adj_fixes (z : Matrix n n R) : (u : Matrix n n R)ᴴ * (J * (a * z)) = J * (a * z) := by
    simpa only [← mul_assoc (u : Matrix n n R), hu_fixes] using preserves_mul (a * z)
  have fixes_adj (z : Matrix n n R) : aᴴ * (J * (u * z)) = aᴴ * (J * z) := by
    conv_lhs => rw [← hu_fixes, conjTranspose_mul, mul_assoc, preserves_mul]
  -- The candidate `x` has the parameter `y c aᴴ`. Both `y (e - 2 c aᴴ J)` and `y` are orthogonal to
  -- `a`, and `u - 1` pairs them to zero. By the rules for `y e`, `J u J - J x J` is this pairing
  -- times `e J`.
  set c : Matrix n n R := e * (u - 1 - a * bᴴ * J * u) * b with hc
  have h_sandwich : J * (u : Matrix n n R) * J - J * radicalElem J (y * c * aᴴ) * J =
      (e - 2 * c * aᴴ * J)ᴴ * (yᴴ * (J * ((u - 1 : Matrix n n R) * y))) * e * J := by
    simp [radicalElem, hc, form_mul_eq_zero hJ ha, ye_mul, ye_adj_mul, preserves_mul, adj_fixes,
      fixes_adj, hJ, mul_assoc, mul_sub, sub_mul, two_mul, add_mul, mul_add]
    abel
  have h_trivial : yᴴ * (J * ((u - 1 : Matrix n n R) * y)) = 0 := by
    simp [sub_mul, mul_sub, hu_trivial y y hy hy]
  rw [h_trivial, mul_zero, zero_mul, zero_mul, sub_eq_zero] at h_sandwich
  exact hJ_unit.mul_left_cancel (hJ_unit.mul_right_cancel h_sandwich)

/-- Reduction in the radical of an isotropic matrix `a`. Let `J` be hermitian and invertible,
`aᴴ J a = aᴴ J y = 0` and `y e + 2 b s aᴴ J = 1`, so that the columns of `y` span `a^⊥`, and let
`u` fix `a` and act trivially on `a^⊥ / a`. Let `r` be any map on matrices; think of `r c` as a
lattice point near `c`, and of `s` as a scaling. Then there are matrices `c`, `d` and an element `x`
of `U J` with matrix `radicalElem J ((a (r d) - y (r c)) s aᴴ)` such that `x` fixes `a` and acts
trivially on `a^⊥ / a`, and `x u` is `radicalElem J ((y (c - r c) - a (d - r d)) s aᴴ)`. -/
lemma exists_radicalElem_mul_eq {u : U J} (hu : (u, 1) ∈ dilationGroup a) (hJ : Jᴴ = J)
    (hJ_unit : IsUnit J) (b s : Matrix n n R) (r : Matrix n n R → Matrix n n R)
    (ha : aᴴ * (J * a) = 0) (hy : aᴴ * (J * y) = 0) (h_split : y * e + 2 * b * s * aᴴ * J = 1) :
    ∃ (c d : Matrix n n R) (x : U J),
      (x : Matrix n n R) = radicalElem J ((a * r d - y * r c) * s * aᴴ) ∧
      (x, 1) ∈ dilationGroup a ∧
      (x : Matrix n n R) * (u : Matrix n n R) =
        radicalElem J ((y * (c - r c) - a * (d - r d)) * s * aᴴ) := by
  -- `u` is `radicalElem J (z aᴴ)` with `z = y c s`, and `x` is `radicalElem J (w aᴴ)`. The
  -- product has the parameter `w + z - a wᴴ J z`, and `d` is chosen so that `wᴴ J z = d s`.
  let c : Matrix n n R := e * (u - 1 - a * (b * s)ᴴ * J * u) * b
  let d : Matrix n n R := -(y * r c * s)ᴴ * J * y * c
  let w : Matrix n n R := (a * r d - y * r c) * s
  have hu_eq : (u : Matrix n n R) = radicalElem J (y * c * s * aᴴ) := by
    simpa only [c, mul_assoc] using eq_radicalElem_of_mem_dilationGroup hu hJ hJ_unit ha hy
      (b := b * s) (by simpa only [mul_assoc] using h_split)
  have hw : aᴴ * (J * w) = 0 := by simp [w, ← mul_assoc, ha, hy, sub_mul, mul_sub]
  have hz : aᴴ * (J * (y * c * s)) = 0 := by simp [form_mul_eq_zero hJ hy, mul_assoc]
  have hd : wᴴ * J * (y * c * s) = d * s := by
    simp [w, d, form_mul_eq_zero hJ hy, sub_mul, mul_assoc]
  have h_param : w + y * c * s - a * (d * s) = (y * (c - r c) - a * (d - r d)) * s := by
    noncomm_ring [w]
  let x : U J := U.of hJ_unit (radicalElem J (w * aᴴ)) (gram_radicalElem hJ ha hw)
  have hx : (x : Matrix n n R) = radicalElem J (w * aᴴ) := rfl
  refine ⟨c, d, x, hx, mem_dilationGroup_of_eq_radicalElem hJ ha hw hx, ?_⟩
  rw [hx, hu_eq, radicalElem_mul hJ ha hw hz, hd, h_param]

variable {E : Type*} [Field E] [CMType E]

/-- The adelic matrix `a` is integral at all finite places and has operator norm at most `r` at
each infinite place. -/
def IsIntBounded (r : ℝ) (a : Matrix n n (𝔸 E)) : Prop :=
  (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)).mapMatrix a ∈ (Ô E).matrix ∧
    ∀ w : NumberField.InfinitePlace E, ‖(evalInf w).mapMatrix a‖ ≤ r

variable {r : ℝ} {a b : Matrix n n (𝔸 E)} {t : ℝ}

lemma IsIntBounded.star (ha : IsIntBounded r a) : IsIntBounded r aᴴ := by
  refine ⟨fun i j ↦ star_mem_Ô (ha.1 j i), fun w ↦ ?_⟩
  exact (norm_star ((evalInf w).mapMatrix a)).trans_le (ha.2 w)

lemma IsIntBounded.nsmul (ha : IsIntBounded r a) (M : ℕ) : IsIntBounded (M * r) (M • a) :=
  ⟨nsmul_mem ha.1 M, fun w ↦ by grw [map_nsmul, norm_nsmul_le, ha.2 w]⟩

lemma IsIntBounded.mul (ha : IsIntBounded r a) (hb : IsIntBounded t b) :
    IsIntBounded (r * t) (a * b) :=
  ⟨by simpa only [map_mul] using mul_mem ha.1 hb.1,
    fun w ↦ by simpa only [map_mul] using norm_mul_le_of_le (ha.2 w) (hb.2 w)⟩

lemma IsIntBounded.sub (ha : IsIntBounded r a) (hb : IsIntBounded t b) :
    IsIntBounded (r + t) (a - b) :=
  ⟨by simpa only [map_sub] using sub_mem ha.1 hb.1,
    fun w ↦ by simpa only [map_sub] using norm_sub_le_of_le (ha.2 w) (hb.2 w)⟩

end New.Reduction

end UnipotentReduction
