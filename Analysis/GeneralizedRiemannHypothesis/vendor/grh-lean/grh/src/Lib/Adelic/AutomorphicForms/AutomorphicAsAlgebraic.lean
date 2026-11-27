import Lib.Adelic.AutomorphicForms.RealConvolution
import Lib.GLn.SchurModule.SchurNorm

/-!
# Automorphic forms on standard definite spaces as algebraic forms

On a standard definite space (`New.Space.IsStd`: all signs `1` and point `x = 1`), this file
identifies automorphic forms with smooth algebraic forms. Let `ρ = New.conjWeylRep κ e` be the
representation of the compact group `G_∞` of weight `(κ, e)`, `d` its dimension, and
`v⁺ = New.highestVector` its highest unit vector when `l` matches the weight. An algebraic form
`φ` (`New.AlgForm`, vector valued on `G_f`) gives `φ♮ = New.ofAlgForm l s φ` with
`φ♮ (x, g) = ⟨v⁺, ρ(x⁻¹) φ(g)⟩`. The inverse map sends a form `y` to
`y♭ g = d ∫ y(x, g) ρ(x) v⁺ dx`. This file also writes integrals over `Γ \ G` as class sums over
`Γ \ G_f`.

## Main definitions and results

* `New.Space.toAlgForm`: the two maps are inverse between forms of type `New.typeKernel l` (fixed by
  `realConv k y (x, g) = ∫ k(z) y(xz, g) dz` for `k = typeKernel l 1`, which is
  `z ↦ d ⟨v⁺, ρ(z) v⁺⟩`) and smooth algebraic forms, by Schur orthogonality, when `l` matches the
  weight (`New.IsHCParam`).
* `New.Space.toAlgForm_formRep`, `New.Space.algFormEquiv`, `New.hasHeckePolynomial_toAlgForm_iff`:
  the equivalence commutes with `G_f`, so it respects levels and Hecke eigenvalues.
* `New.Space.integral_eq_classIntegral_of_isLevel`,
  `New.Space.integral_mul_eq_classIntegral_toAlgFormFun`, `New.Space.integral_mul_eq_classIntegral`:
  integrals over `Γ \ G`, in particular against `φ♮`, as class sums `New.classIntegral` over
  `Γ \ G_f`.
* `New.Space.classSum_gramForm_eq_mul_petersson`: for two algebraic forms that transform under a
  level by one character with values of finite order, the class sum of their Gram pairings is a
  multiple of the Petersson product of the associated functions.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s), for the signs s, at the infinite places and 1 at the finite places.
* `New.Space.IsAutomorphic`: a function on `G = G_∞ × G_f` that is continuous, left invariant under
  rational points and right invariant under an open subgroup of `G_f`.
* `New.algFormCoeff s L φ`: the function `(x, g) ↦ L (ρ(x⁻¹) φ(g))`; it is `New.ofAlgForm l s φ` for
  `L = ⟨v⁺, ·⟩`, where `⟨·, ·⟩ = New.gramForm`.
* `New.stdLevelIndex K`: the index `[stdLevel : K ∩ stdLevel]` in the standard level
  `stdLevel = New.stdLevel E n`; a level (`New.IsLevel K`) is an open subgroup `K ≤ stdLevel`.
* `New.classIntegral Γ K f`: the integral of `f` over `Γ \ G_f` for `vol K = 1`, as a finite sum; in
  this file `Γ = New.stdRatPoints`, the rational points of the standard space.

## Relation to the literature

Known result: algebraic modular forms as functions on the adelic group. For the source see
`Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms`.
-/

noncomputable section

namespace New

open NumberField MeasureTheory Fintype Subgroup DiscreteSeries

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ} {l : InfinitePlace E → n → ℤ} {s : n → ℤˣ}
  {V : Space E n s} {φ : AlgForm n κ e}

lemma isStd_signedSpace [HasPrimitiveRoot5040 E] (hs : s = 1) : (signedSpace E s).IsStd where
  signs_eq_one := hs
  point_eq_one := by aesop

/-- The matrix `conjWeylMatrix κ e x` depends continuously on the archimedean point `x`. -/
lemma continuous_conjWeylMatrix (κ : InfinitePlace E → ℕ → ℕ) (e : InfinitePlace E → ℤ)
    (s : n → ℤˣ) : Continuous fun x : GInf E s ↦ conjWeylMatrix κ e x := by
  -- Column `b` is the image of the `b`-th basis vector under `conjWeylRep κ e x`.
  refine continuous_matrix fun a b ↦ ?_
  have h_entry (x : GInf E s) :
      conjWeylMatrix κ e x a b = conjWeylRep κ e x (Pi.single b 1) a :=
    (congrFun (Matrix.mulVec_single_one (conjWeylMatrix κ e x) b) a).symm
  simp only [h_entry]
  exact (continuous_apply a).comp (continuous_conjWeylRep (Pi.single b 1))

namespace Space

/-! ### The maps `φ ↦ φ♮` and `y ↦ y♭` -/

/-- The coefficient of a translated algebraic form is the translated coefficient:
`algFormCoeff` turns `algFormRep κ e a` into right translation by `(1, a)`. -/
lemma algFormCoeff_algFormRep (L : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) (a : Gf E n) (g : G E s) :
    algFormCoeff s L (algFormRep κ e a φ) g = algFormCoeff s L φ (g * (1, a)) := by
  -- The archimedean component is unchanged, and `algFormRep` translates `φ` on the right by `a`.
  simp [algFormCoeff_apply]

variable (φ) in
/-- Let V be standard and φ an algebraic form of weight (κ, e) (so its stabiliser under right
translation is open). For every linear functional L, the function g ↦ L(ρ(g_∞⁻¹) φ(g_f)) on G
(`New.algFormCoeff`) is automorphic. -/
lemma isAutomorphic_algFormCoeff [hV : V.IsStd] {L : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ} :
    V.IsAutomorphic (algFormCoeff s L φ) := by
  induction hV
  obtain ⟨φ_open, φ_rat⟩ := φ.property
  let K : OpenSubgroup (Gf E n) := ⟨rightStabilizer φ.val, φ_open⟩
  -- `φ` is fixed by the right translations in a neighbourhood of `1`, so it is locally constant
  have φ_cont : Continuous φ.val := (isLocallyConstant_of_eventually_mul K.mem_nhds_one).continuous
  refine ⟨?_, ?_, K, fun k hk ↦ by simp [hk _, algFormCoeff_apply]⟩
  · -- `(x, g) ↦ ρ(x⁻¹) φ(g)` is a continuous matrix applied to a continuous vector
    exact L.continuous_on_pi.comp
      (((continuous_conjWeylMatrix κ e 1).comp continuous_fst.inv).matrix_mulVec φ_cont.snd')
  · -- a rational `γ` moves `φ` by its archimedean component, which cancels against `ρ(x⁻¹)`
    rintro _ ⟨γ, rfl⟩ g
    have h_rat : φ.val (((stdSpace E n).ratEmbed γ).2 * g.2) =
        weightRep κ e (stdSpace E n) γ (φ.val g.2) := φ_rat γ g.2
    simp [algFormCoeff_apply, weightRep, h_rat]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : InfinitePlace E → ℕ → ℕ}
  {e : InfinitePlace E → ℤ} {l : InfinitePlace E → n → ℤ} in
variable (κ e l) in
/-- The function `y♭` on `G_f` attached to a function `y` on the definite group:
`y♭ g = d ∫ y (x, g) • x v` over `G_∞`, where `d` is the dimension of the Weyl module, `x` acts by
`conjWeylRep` and `v` is the highest vector. -/
def toAlgFormFun (y : G E (1 : n → ℤˣ) → ℂ) (g : Gf E n) : WeylIndex n κ → ℂ :=
  ∫ x : GInf E (1 : n → ℤˣ),
    (card (WeylIndex n κ) * y (x, g)) • conjWeylRep κ e (s := 1) x (highestVector κ l)

/-- If `y` is automorphic on the standard space, then `y♭ = toAlgFormFun κ e l y` is an algebraic
form: its stabiliser is open and it is equivariant under rational points. -/
lemma toAlgFormFun_mem_algForm {y : G E (1 : n → ℤˣ) → ℂ}
    (hy : (stdSpace E n).IsAutomorphic y) : toAlgFormFun κ e l y ∈ AlgForm n κ e := by
  obtain ⟨hy_cont, hy_rat, K, hK⟩ := hy
  refine ⟨?_, fun γ g ↦ ?_⟩
  · -- An open subgroup `K` fixing `y` lies in the stabiliser of `y♭`, which is therefore open.
    exact isOpen_mono (H₁ := K.1) (fun k hk g ↦ by simp [toAlgFormFun, ← hK k hk ⟨_, g⟩]) K.2
  · -- Translate the integral over `G_∞` by `γ` and use the invariance of `y` under `γ`.
    calc toAlgFormFun κ e l y ((stdSpace E n).embFin γ * g)
      _ = ∫ x, (card (WeylIndex n κ) * y ((stdSpace E n).ratEmbed γ * (x, g))) •
            conjWeylRep κ e (((stdSpace E n).ratEmbed γ).1 * x) (highestVector κ l) :=
        (integral_mul_left_eq_self _ ((stdSpace E n).ratEmbed γ).1).symm
      _ = ∫ x, weightRep κ e (stdSpace E n) γ
            ((card (WeylIndex n κ) * y (x, g)) • conjWeylRep κ e x (highestVector κ l)) := by
        simp [hy_rat _ ⟨γ, rfl⟩, weightRep]
      _ = weightRep κ e (stdSpace E n) γ (toAlgFormFun κ e l y g) :=
        (weightRep κ e (stdSpace E n) γ).toContinuousLinearMap.integral_comp_comm
          integrable_of_compactSpace

/-- Let `l` be twice the Harish-Chandra parameter of the weight `(κ, e)`. The convolution over
`G_∞` of a continuous `y` with `typeKernel l 1` is `(x, g) ↦ ⟨v, x⁻¹ y♭(g)⟩`, where `v` is the
highest vector and `y♭ = toAlgFormFun κ e l y`. -/
lemma realConv_typeKernel (h : IsHCParam (n := n) κ e l) {y : G E (1 : n → ℤˣ) → ℂ}
    (hy : Continuous y) (g : G E (1 : n → ℤˣ)) :
    realConv (typeKernel l 1) y g =
      gramForm (highestVector κ l) (conjWeylRep κ e g.1⁻¹ (toAlgFormFun κ e l y g.2)) := by
  obtain ⟨x, g⟩ := g
  -- `typeKernel l 1` is the dimension times the matrix coefficient at `v`.
  have h_kernel (z : GInf E (1 : n → ℤˣ)) : typeKernel l 1 z = card (WeylIndex n κ) *
      gramForm (highestVector κ l) (conjWeylRep κ e z (highestVector κ l)) := by
    simp [h.prod_formalDegree, h.gramForm_conjWeylRep_eq_dsCoeff, ← Complex.ofReal_prod,
      typeKernel, dsKernel, Finset.prod_mul_distrib, -card_pi]
  let L : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ := gramForm (highestVector κ l) ∘ₗ conjWeylRep κ e x⁻¹
  symm
  calc L (toAlgFormFun κ e l y g)
      = ∫ z, L ((card (WeylIndex n κ) * y (z, g)) • conjWeylRep κ e z (highestVector κ l)) :=
        (L.toContinuousLinearMap.integral_comp_comm integrable_of_compactSpace).symm
    _ = ∫ z, L ((card (WeylIndex n κ) * y (x * z, g)) •
          conjWeylRep κ e (x * z) (highestVector κ l)) :=
        (integral_mul_left_eq_self _ x).symm
    _ = realConv (typeKernel l 1) y (x, g) := by
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        simp [L, h_kernel, mul_assoc, mul_comm (y (x * z, g))]

/-- Let `l` be twice the Harish-Chandra parameter of `(κ, e)` and `ψ` an algebraic form of weight
`(κ, e)`. Then `(ψ♮)♭ = ψ`. Here `ψ♮ = ofAlgForm l 1 ψ` is the function `g ↦ ⟨v⁺, ρ(g_∞⁻¹) ψ(g_f)⟩`
on the group of the standard space, with `v⁺` the highest vector for `l`. For a function `y` on that
group, `y♭ = toAlgFormFun κ e l y` is `g ↦ d ∫_{G_∞} y(x, g) ρ(x) v⁺ dx`, with `d` the dimension of
the Weyl module and `ρ = conjWeylRep`. -/
lemma toAlgFormFun_ofAlgForm (h : IsHCParam (n := n) κ e l) (ψ : AlgForm n κ e) :
    toAlgFormFun κ e l (ofAlgForm l 1 ψ) = ψ.val := by
  -- Schur orthogonality at the unit vector `v = highestVector κ l`, one coordinate at a time.
  funext g a
  let v : WeylIndex n κ → ℂ := highestVector κ l
  have h_cont : Continuous (ofAlgForm l 1 ψ) :=
    ((stdSpace E n).isAutomorphic_algFormCoeff ψ).continuous
  have h_int (b : WeylIndex n κ) : Integrable fun x : GInf E (1 : n → ℤˣ) ↦
      ((card (WeylIndex n κ) * ofAlgForm (κ := κ) l 1 ψ (x, g)) • conjWeylRep κ e x v) b :=
    integrable_of_compactSpace (by fun_prop (disch := simp))
  calc toAlgFormFun κ e l (ofAlgForm l 1 ψ) g a
    _ = card (WeylIndex n κ) * ∫ x, LinearMap.proj (R := ℂ) a (conjWeylRep κ e (s := 1) x v) *
          gramForm v (conjWeylRep κ e x⁻¹ (ψ.1 g)) := by
      rw [toAlgFormFun, eval_integral h_int, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [v, algFormCoeff_apply, Pi.smul_apply, smul_eq_mul, LinearMap.proj_apply]
      ring
    _ = ψ.1 g a := by
      rw [schur_orthogonality, gramForm_highestVector_self fun w ↦ (h w).1, mul_one,
        LinearMap.proj_apply, mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 card_ne_zero)]

/-- Let `V` be standard (all its signs `s` are +1 and its point is the identity matrix) and `l`
twice the Harish-Chandra parameter of `(κ, e)`. For every algebraic form `ψ`, the function
`ofAlgForm l s ψ`, g ↦ ⟨v⁺, ρ(g_∞⁻¹) ψ(g_f)⟩, is a form of type `typeKernel l s`. That kernel is the
product over the infinite places of the formal degree times the conjugate discrete series
coefficient. That is, this function is automorphic, bounded and fixed by convolution with that
kernel over `G_∞`. -/
lemma isForm_ofAlgForm [hV : V.IsStd] (h : IsHCParam (n := n) κ e l) (ψ : AlgForm n κ e) :
    V.IsForm (typeKernel l s) (ofAlgForm l s ψ) := by
  -- `V.IsStd` leaves only the standard space: `s = 1` and the point is the identity.
  induction hV
  have h_aut : (stdSpace E n).IsAutomorphic (ofAlgForm l 1 ψ) :=
    (stdSpace E n).isAutomorphic_algFormCoeff ψ
  refine ⟨h_aut, (h_aut.mem_rapidFunctions fun _ _ ↦ rfl).2.bounded, fun _ ↦ funext fun g ↦ ?_⟩
  rw [realConv_typeKernel h h_aut.continuous, toAlgFormFun_ofAlgForm h, algFormCoeff_apply]

/-! ### The equivalence and its equivariance -/

variable (V) in
/-- On a standard space, for `l` twice the Harish-Chandra parameter of `(κ, e)`, the forms of type
`typeKernel l s` are the smooth algebraic forms of weight `(κ, e)`. This is the inverse `y ↦ y♭` of
`φ ↦ φ♮ = ofAlgForm l s φ`, which is injective as `(φ♮)♭ = φ`, and surjective as `y = (y♭)♮`. -/
def toAlgForm [hV : V.IsStd] (h : IsHCParam (n := n) κ e l) :
    V.Form (typeKernel l s) ≃ₗ[ℂ] AlgForm n κ e :=
  .symm <| .ofBijective ((ofAlgForm l s).codRestrict _ (isForm_ofAlgForm h)) <| by
    induction hV
    refine ⟨fun φ ψ h_eq ↦ Subtype.ext ?_, ?_⟩
    · rw [← toAlgFormFun_ofAlgForm h φ, ← toAlgFormFun_ofAlgForm h ψ]
      exact congrArg (toAlgFormFun κ e l) (congrArg Subtype.val h_eq)
    rintro ⟨y, hy⟩
    let φ : AlgForm n κ e := ⟨toAlgFormFun κ e l y, toAlgFormFun_mem_algForm hy.toIsAutomorphic⟩
    refine ⟨φ, Subtype.ext ?_⟩
    calc ofAlgForm l 1 φ = realConv (typeKernel l 1) y :=
          funext fun g ↦ (realConv_typeKernel h hy.continuous g).symm
      _ = y := hy.realConv_eq integrable_of_compactSpace

/-- Let `V` be a standard space and `l` twice the Harish-Chandra parameter of `(κ, e)`. Let `y` be a
form of type `typeKernel l s` on `V`, and let `φ = V.toAlgForm h y` be its algebraic form of weight
`(κ, e)`. Then `ofAlgForm l s φ` gives `y` back: `y(g) = ⟨v⁺, ρ(g_∞⁻¹) φ(g_f)⟩`, with `v⁺` the
highest vector for `l`. -/
lemma ofAlgForm_toAlgForm [V.IsStd] (h : IsHCParam (n := n) κ e l)
    (y : V.Form (typeKernel l s)) :
    ofAlgForm l s (V.toAlgForm h y) = y :=
  congrArg Subtype.val ((V.toAlgForm h).left_inv y)

/-- Let `l` be twice the Harish-Chandra parameter of `(κ, e)` and `y` a form of type
`typeKernel l 1` on the standard space. The algebraic form `toAlgForm h y` corresponds to `y` under
the inverse of `φ ↦ ofAlgForm l 1 φ`. Its underlying function is `y♭ = toAlgFormFun κ e l y`, i.e.
`g ↦ d ∫_{G_∞} y(x, g) ρ(x) v⁺ dx`, with `d` the dimension of the Weyl module, `ρ = conjWeylRep` and
`v⁺` the highest vector for `l`. -/
theorem toAlgForm_eq_toAlgFormFun (h : IsHCParam (n := n) κ e l)
    (y : (stdSpace E n).Form (typeKernel l 1)) :
    ((stdSpace E n).toAlgForm h y).val = toAlgFormFun κ e l y.val := by
  rw [← toAlgFormFun_ofAlgForm h, ofAlgForm_toAlgForm]

/-- For `l` twice the Harish-Chandra parameter of `(κ, e)`, the isomorphism `New.Space.toAlgForm`
from forms of type `typeKernel l s` on a standard space to smooth algebraic forms of weight
`(κ, e)` commutes with right translation by `G_f`. -/
@[local simp]
lemma toAlgForm_formRep [V.IsStd] (h : IsHCParam (n := n) κ e l) (a : Gf E n)
    (y : V.Form (typeKernel l s)) :
    V.toAlgForm h (V.formRep (typeKernel l s) a y) = algFormRep κ e a (V.toAlgForm h y) := by
  -- Apply the inverse `ofAlgForm`, which commutes with right translation.
  apply (V.toAlgForm h).symm.injective
  refine (LinearEquiv.symm_apply_apply _ _).trans (Subtype.ext (funext fun g ↦ ?_))
  calc y.1 (g * (1, a)) = ofAlgForm l s (V.toAlgForm h y) (g * (1, a)) :=
      (congrFun (ofAlgForm_toAlgForm h y) _).symm
    _ = ofAlgForm l s (algFormRep κ e a (V.toAlgForm h y)) g :=
      (algFormCoeff_algFormRep _ a g).symm

variable (V) in
/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), the isomorphism
φ ↦ `ofAlgForm l s φ` from K-fixed algebraic forms to K-fixed forms of type `typeKernel l s`. No
hypothesis is put on K. -/
def algFormEquiv [V.IsStd] (h : IsHCParam (n := n) κ e l) (K : Subgroup (Gf E n)) :
    levelSpace (algFormRep κ e) K ≃ₗ[ℂ] levelSpace (V.formRep (typeKernel l s)) K :=
  -- `V.toAlgForm h` is equivariant, so it matches the vectors fixed by `K`.
  (V.toAlgForm h).symm.ofSubmodules (levelSpace (algFormRep κ e) K)
    (levelSpace (V.formRep (typeKernel l s)) K) <| by
    ext
    simp [-toAlgForm_formRep, ← toAlgForm_formRep]

variable (V) in
/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), a form y of type
`typeKernel l s` has Hecke polynomial p at the place w (with `star w ≠ w`) if and only if its
algebraic form, as a function on G_f, does. (`HasHeckePolynomial`: fixed by the standard group at w
and an eigenvector of the Hecke operators there, as prescribed by p; `WeilData E`: the auxiliary
element, idele and splitting character fixed on E.) -/
lemma _root_.New.hasHeckePolynomial_toAlgForm_iff [V.IsStd] (h : IsHCParam (n := n) κ e l)
    [WeilData E] {y : V.Form (typeKernel l s)} {w : FinPlace E} {p : ℂ → ℂ} {hw : star w ≠ w} :
    HasHeckePolynomial (rightRegular ℂ (Gf E n) (WeylIndex n κ → ℂ)) hw p (V.toAlgForm h y).val ↔
      HasHeckePolynomial (V.formRep (typeKernel l s)) hw p y := by
  -- `L` sends a form to its algebraic form, as a function; it is injective and equivariant.
  let L : V.Form (typeKernel l s) →ₗ[ℂ] Gf E n → WeylIndex n κ → ℂ :=
    (AlgForm n κ e).subtype ∘ₗ (V.toAlgForm h).toLinearMap
  have L_inj : Function.Injective L := Subtype.val_injective.comp (V.toAlgForm h).injective
  have L_hecke (X : ℂ) : L (heckePolyOp (V.formRep _) hw X y) =
      heckePolyOp (rightRegular ℂ (Gf E n) (WeylIndex n κ → ℂ)) hw X (L y) :=
    map_heckePolyOp L X (by simp [L])
  simp [HasHeckePolynomial, ← L_inj.eq_iff, L_hecke, L]

/-! ### Integrals over the quotient as class sums -/

/-- On a standard definite space `V` let `F` be automorphic and `K` a level (an open subgroup of the
standard level `stdLevel`). The integral of `F` over `Γ \ G` is `[stdLevel : K]⁻¹` times the class
integral at level `K` (normalised by `vol K = 1`) of `g ↦ ∫ F(x, g) dx` over `x ∈ G_∞`. -/
lemma integral_eq_classIntegral_of_isLevel [hV : V.IsStd] {F : G E s → ℂ}
    (hF : V.IsAutomorphic F) {K : Subgroup (Gf E n)} (hK : IsLevel K) :
    ∫ g : G E s, F g ∂V.quotMeasure =
      (stdLevelIndex K : ℂ)⁻¹ *
        classIntegral stdRatPoints K fun g : Gf E n ↦ ∫ x : GInf E s, F (x, g) := by
  obtain ⟨h_cont, h_left, K', h_right⟩ := hF
  induction hV -- now `s = 1` and `V` is the standard space
  -- For the level `S = Stab f ∩ K`, the integral is `[stdLevel : S]⁻¹` times the class sum of `f`
  -- at `S`, and `[stdLevel : S] = [K : S] [stdLevel : K]`; the factor `[K : S]⁻¹` is the one in
  -- `classIntegral`.
  set f : Gf E n → ℂ := fun g ↦ ∫ x, F (x, g)
  set S : Subgroup (Gf E n) := rightStabilizer f ⊓ K
  have hK' : (K' : Subgroup (Gf E n)) ≤ rightStabilizer f := fun k hk g ↦ by
    simp [f, ← h_right k hk ⟨_, g⟩]
  have : IsLevel S :=
    ⟨inf_le_of_right_le hK.le, (isOpen_mono hK' K'.isOpen).inter hK.isOpen⟩
  have h_index : (stdLevelIndex S : ℂ) = (rightStabilizer f).relIndex K * stdLevelIndex K := by
    rw [← inf_relIndex_right, ← Nat.cast_mul, relIndex_mul_relIndex _ _ _ inf_le_right hK.le]
  calc ∫ g, F g ∂(stdSpace E n).quotMeasure
    _ = (stdLevelIndex S : ℂ)⁻¹ * classSum stdRatPoints S f :=
      integral_quotMeasure_eq_classSum h_left (fun _ ↦ rfl) S inf_le_left h_cont
    _ = (stdLevelIndex K : ℂ)⁻¹ *
        (((rightStabilizer f).relIndex K : ℂ)⁻¹ * classSum stdRatPoints S f) := by
      rw [h_index, mul_inv_rev, mul_assoc]
    _ = _ := by rw [classIntegral, inv_natCast_smul_eq ℚ ℂ, smul_eq_mul]

/-- Let `K` be a level. Let `y`, `y'` be automorphic functions on the group `G` of the standard
space: continuous, left `Γ`-invariant, and right invariant under an open subgroup of `G_f`. Suppose
`y'(x, g) = L g (ρ(x) v⁺)` for linear functionals `L g`, where `ρ = conjWeylRep` and `v⁺` is the
highest vector for `l`. Then `d ∫_{Γ\G} y' y` (for `quotMeasure`, with `d` the dimension of the Weyl
module) equals `(stdLevelIndex K)⁻¹ = [stdLevel : K]⁻¹` times the `classIntegral` at `K` of
`g ↦ L g (y♭ g)`, i.e. the integral over `Γ \ G_f` for `vol K = 1`, where
`y♭ g = d ∫_{G_∞} y(x, g) ρ(x) v⁺ dx` is `toAlgFormFun κ e l y`. -/
theorem integral_mul_eq_classIntegral_toAlgFormFun (K : Subgroup (Gf E n)) [hK : IsLevel K]
    {y y' : G E (1 : n → ℤˣ) → ℂ} (hy : (stdSpace E n).IsAutomorphic y)
    (hy' : (stdSpace E n).IsAutomorphic y')
    (L : Gf E n → (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ)
    (hy'_eq : ∀ (x : GInf E (1 : n → ℤˣ)) (g : Gf E n),
      y' (x, g) = L g (conjWeylRep κ e x (highestVector κ l))) :
    (card (WeylIndex n κ) : ℂ) * ∫ g : G E (1 : n → ℤˣ), y' g * y g ∂(stdSpace E n).quotMeasure =
      (stdLevelIndex K : ℂ)⁻¹ *
        classIntegral stdRatPoints K fun g : Gf E n ↦ L g (toAlgFormFun κ e l y g) := by
  set d : ℂ := ((card (WeylIndex n κ) : ℕ) : ℂ)
  have h_cont : Continuous y := hy.continuous
  -- Integrate over `G_∞` first.
  have h_infinite (g : Gf E n) :
      ∫ x, d * (y' (x, g) * y (x, g)) = L g (toAlgFormFun κ e l y g) := by
    calc ∫ x, d * (y' (x, g) * y (x, g))
      _ = ∫ x, L g ((d * y (x, g)) • conjWeylRep κ e (s := 1) x (highestVector κ l)) := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp [hy'_eq, mul_comm, mul_assoc]
      _ = L g (toAlgFormFun κ e l y g) :=
        (L g).toContinuousLinearMap.integral_comp_comm integrable_of_compactSpace
  rw [← integral_const_mul, integral_eq_classIntegral_of_isLevel
    (hy'.map₂ hy fun a b ↦ d * (a * b)) hK]
  simp only [h_infinite]

/-- Let `V` be standard, `l` twice the Harish-Chandra parameter of `(κ, e)`, `φ` an algebraic form,
`K` a level and `Φ` automorphic. If `Φ (x, g) = L g (ρ(x) v⁺)` with each `L g` linear,
`ρ = conjWeylRep κ e`, `v⁺ = highestVector κ l`, then the integral of `Φ` times `ofAlgForm l s φ`
over `Γ \ G` is `(dim ρ * stdLevelIndex K)⁻¹` times the integral of `g ↦ L g (φ g)` over `Γ \ G_f`,
normalised by `vol K = 1`. -/
lemma integral_mul_eq_classIntegral [hV : V.IsStd] (h_param : IsHCParam (n := n) κ e l)
    (K : Subgroup (Gf E n)) [IsLevel K] {Φ : G E s → ℂ} (hΦ : V.IsAutomorphic Φ)
    (L : Gf E n → (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ)
    (hΦ_eq : ∀ (x : GInf E s) (g : Gf E n),
      Φ (x, g) = L g (conjWeylRep κ e x (highestVector κ l))) :
    ∫ g : G E s, Φ g * ofAlgForm l s φ g ∂V.quotMeasure =
      (card (WeylIndex n κ) * stdLevelIndex K : ℂ)⁻¹ *
        classIntegral stdRatPoints K fun g : Gf E n ↦ L g (φ.val g) := by
  -- `V.IsStd` leaves only the standard space, where `(φ♮)♭ = φ` for `φ♮ = ofAlgForm l 1 φ`.
  induction hV
  rw [mul_inv, mul_assoc, eq_inv_mul_iff_mul_eq₀ (Nat.cast_ne_zero.2 card_ne_zero),
    ← toAlgFormFun_ofAlgForm h_param φ]
  exact integral_mul_eq_classIntegral_toAlgFormFun K (isAutomorphic_algFormCoeff φ) hΦ L hΦ_eq

/-- When all signs are `1`, the conjugate of `ofAlgForm l s φ (x, g) = ⟨v⁺, ρ(x⁻¹) φ(g)⟩` is
`⟨φ(g), ρ(x) v⁺⟩`, where `⟨·, ·⟩ = gramForm`, `ρ = conjWeylRep κ e` and
`v⁺ = highestVector κ l`. -/
lemma star_ofAlgForm (h : s = 1) (x : GInf E s) (g : Gf E n) :
    star (ofAlgForm l s φ (x, g)) = gramForm (φ.val g) (conjWeylRep κ e x (highestVector κ l)) := by
  subst h
  simp [← gramForm_conjWeylRep (e := e) x⁻¹ (φ.1 _), conj_gramForm, algFormCoeff_apply]

variable (V) in
/-- Let `V` be standard (all signs `+1`, point the identity), `l` twice the Harish-Chandra parameter
of `(κ, e)`, `K` a level and `χ` a character of `K` whose values have finite order. For algebraic
forms `φ`, `φ'` on which `K` acts by `χ`, the class sum at `K` (over `Γ\G_f/K`, the term at `g`
weighted by `1/#(Γ ∩ gKg⁻¹)`) of the Gram pairings `⟨φ(g), φ'(g)⟩` is the index
`stdLevelIndex K = [stdLevel : K]`, times the dimension of the weight, times the Petersson product
`∫_{Γ\G} conj(F_φ) F_φ'`, where `F_φ = ofAlgForm l s φ` is the function
`F_φ(g) = ⟨v⁺, ρ(g_∞⁻¹) φ(g_f)⟩` on the group. -/
theorem classSum_gramForm_eq_mul_petersson [hV : V.IsStd] (h : IsHCParam (n := n) κ e l)
    (K : Subgroup (Gf E n)) [IsLevel K] (χ : K →* ℂ) (hχ : ∀ k : K, IsOfFinOrder (χ k))
    {φ φ' : AlgForm n κ e}
    (hφ : φ ∈ levelSpace (algFormRep κ e) K χ) (hφ' : φ' ∈ levelSpace (algFormRep κ e) K χ) :
    classSum stdRatPoints K (fun g : Gf E n ↦ gramForm (φ.val g) (φ'.val g)) =
      (stdLevelIndex K : ℂ) * (card (WeylIndex n κ) : ℂ) *
        V.petersson (ofAlgForm l s φ) (ofAlgForm l s φ') := by
  -- The Petersson product is an integral over `Γ \ G`, hence a multiple of the class integral of
  -- the Gram pairings. As `χ` has values of norm `1`, these are fixed by `K`: it is the class sum.
  have h_pet :
      V.petersson (ofAlgForm l s φ) (ofAlgForm l s φ') =
        (card (WeylIndex n κ) * stdLevelIndex K : ℂ)⁻¹ *
          classIntegral stdRatPoints K fun g : Gf E n ↦ gramForm (φ.val g) (φ'.val g) :=
    integral_mul_eq_classIntegral h K (isForm_ofAlgForm h φ).conj.toIsAutomorphic
      (fun g : Gf E n ↦ gramForm (φ.val g)) (star_ofAlgForm hV.signs_eq_one)
  have h_fix : K ≤ rightStabilizer fun g : Gf E n ↦ gramForm (φ.val g) (φ'.val g) := by
    intro k hk g
    have h_left : φ.val (g * k) = χ ⟨k, hk⟩ • φ.val g :=
      congrFun (congrArg Subtype.val (hφ ⟨k, hk⟩)) g
    have h_right : φ'.val (g * k) = χ ⟨k, hk⟩ • φ'.val g :=
      congrFun (congrArg Subtype.val (hφ' ⟨k, hk⟩)) g
    simp [h_left, h_right, ← mul_assoc, RCLike.mul_conj, (hχ ⟨k, hk⟩).norm_eq_one]
  have h_card : (card (WeylIndex n κ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr card_ne_zero
  have h_index : (stdLevelIndex K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (isCompact_stdLevel.relIndex_ne_zero IsLevel.isOpen)
  rw [h_pet, ← classIntegral_eq_classSum h_fix]
  field_simp

end Space

end New

end
