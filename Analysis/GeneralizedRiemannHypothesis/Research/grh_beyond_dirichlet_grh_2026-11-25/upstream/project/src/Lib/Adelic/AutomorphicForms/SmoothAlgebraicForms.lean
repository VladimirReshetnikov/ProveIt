import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.GLn.SchurModule.SchurOrthogonality
import Lib.GaloisRep.Main.Defs
import Lib.Weil.Construction.ThetaJets

/-!
# Algebraic forms on definite unitary groups, their pairing and Harish-Chandra parameters

This file studies forms on the definite unitary group of a hermitian space. A weight `(κ, e)`
records, at each infinite place `τ`, the number `κ τ h` of columns of height `h` of a Young diagram
and the power `e τ` of the determinant.

## Main definitions and results

* `New.AlgForm`: functions `φ` on the finite adelic points `New.Gf` with `φ(γ g) = ρ(γ) φ(g)` for
  rational `γ`, where `ρ = New.Space.weightRep`, whose stabiliser under right translation is open;
  `New.algFormRep` is right translation.
* `New.algFormCoeff`, `New.ofAlgForm`: from a form `φ` to the function `(x, g) ↦ L (ρ(x⁻¹) φ(g))`,
  `ρ = New.conjWeylRep`, for any linear form `L` and for the pairing with `New.highestVector`.
* `New.smoothPairing`, `New.smoothPairing_formTranslation`: a pairing B of coefficient vectors
  invariant under `New.Space.weightRep` gives a pairing of forms, by integration over Γ\G_f,
  invariant under G_f.
* `New.IsHCParam.eq_hcParameter`, `New.IsHCParam.exists_decreasingPosition_eq`: the entries of a
  parameter `l` are those of `New.hcParameter`, in the decreasing order of `l`;
  `New.IsHCParam.lowestKType_eq`: the highest weight that `l` determines.
* `New.highestVector_cyclic`: for injective `l w` and signs all 1, the highest vector
  `New.highestVector` of `New.conjWeylRep` is cyclic (`New.span_translate_highestVector_eq_top`),
  and so is its dual (`New.span_gramForm_highestVector_comp_eq_top`).
* `New.IsHCParam.prod_formalDegree`: the product of the formal degrees `New.HCParam.formalDegree` is
  the dimension.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.Space.embFin`: For a space (J, x), the homomorphism U(J)(E) → G_f sending γ to the finite
  part of x^{-1} γ x.
* `New.conjWeylRep`: The complex linear representation of weight (κ, e) of the product over places
  of the unitary groups of signs s, acting by the matrices `New.conjWeylMatrix`.
* `New.IsHCParam`: `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)`, in some
  order: at each place `w` the numbers `l w i` are distinct, and each of them is
  `hcParameter κ e (card n) w p` for some position `p < card n`.
* `New.HCParam.dsCoeff`: The function c_λ(g) = Ξ(a, a⁻¹g) of a complex matrix g, with a the block
  diagonal part of g and Ξ the normalised integral `New.HCParam.flenstedJensen`.

## Relation to the literature

Known result: algebraic modular forms on definite unitary groups, their invariant pairing and
Harish-Chandra parameters. Source: B. Gross, Algebraic modular forms, Israel J. Math. 113 (1999).
-/

noncomputable section

namespace New

/-!
## Smooth forms for a group with rational points

Smooth forms for a group `G` with rational points `e : Γ →* G` and a representation `ρ` of `Γ` on
`V`.
-/

section SmoothForms

variable {G Γ V : Type*} [Group G] [Group Γ] [AddCommGroup V] [Module ℂ V] [TopologicalSpace G]
  [IsTopologicalGroup G] (e : Γ →* G) (ρ : Representation ℂ Γ V)

/-- Smooth forms: functions φ : G → V with φ(e(γ)g) = ρ(γ)φ(g) whose stabiliser under right
translation is open. -/
def SmoothForm : Submodule ℂ (G → V) := (smoothFunctions ℂ).toSubmodule ⊓ ρ.coindV e

/-- The representation of G on smooth forms by right translation. -/
@[simps! -fullyApplied apply_apply_coe]
def smoothFormRep : Representation ℂ G (SmoothForm e ρ) :=
  (rightRegular ℂ G V).subrepresentation (SmoothForm e ρ) fun a φ ⟨h_smooth, h_equivariant⟩ ↦ by
    refine ⟨(smoothFunctions ℂ).apply_mem_toSubmodule a h_smooth, fun γ g ↦ ?_⟩
    simp [mul_assoc, h_equivariant γ]

end SmoothForms

/-!
## Algebraic forms and a p-adic gauge of their values

The spaces of algebraic modular forms on the definite unitary group of the sum of `n` norms
(`New.stdSpace`), and the measure of their `p`-adic integrality.

* `New.weylGauge`: the largest `p`-adic size of a coordinate of the translate of a value `ξ` by
  the inverse of a finite adelic point `g`.

Values are coordinate vectors indexed by `New.WeylIndex`, on which matrices over any commutative
ring act by `New.weylRep`.
-/

section AlgFormDefs

open NumberField Matrix Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  (κ : InfinitePlace E → ℕ → ℕ) (e : InfinitePlace E → ℤ) {s : n → ℤˣ}
  {p : ℕ} [Fact p.Prime] [ι : PadicPlace p]

/-- The representation of the rational unitary group U(J)(E) on coordinate vectors of weight
(κ, e), through its components at the infinite places and `New.conjWeylRep`. A component acts
through its entrywise conjugate, which for signs all 1 is its inverse transpose. -/
@[simps! -isSimp apply]
def Space.weightRep (V : Space E n s) : Representation ℂ (U V.J) (WeylIndex n κ → ℂ) :=
  (conjWeylRep κ e).comp ((MonoidHom.fst (InfinitePlace E → USign s) (Gf E n)).comp V.ratEmbed)

variable (n) in
/-- Smooth algebraic forms of weight (κ, e) on the standard space `New.stdSpace E n`: functions φ on
the finite adelic unitary group with φ(γg) = ρ(γ)φ(g) for rational γ whose stabiliser under right
translation is open. -/
abbrev AlgForm : Submodule ℂ (Gf E n → WeylIndex n κ → ℂ) :=
  SmoothForm (stdSpace E n).embFin (weightRep κ e (stdSpace E n))

/-- The representation of the finite adelic unitary group on the space of algebraic forms of
weight (κ,e), by right translation. -/
abbrev algFormRep :
    Representation ℂ (Gf E n) (SmoothForm (stdSpace E n).embFin (weightRep κ e (stdSpace E n))) :=
  smoothFormRep (stdSpace E n).embFin (weightRep κ e (stdSpace E n))

/-- The gauge of ξ at g: the largest p-adic absolute value of a coordinate of g⁻¹·ι(ξ), where
ι = `ιₚ` maps ℂ to the p-adic field and g⁻¹ acts in weight (κ, e), at τ through the p-adic
component given by the embedding `weightEmbedding ιₚ τ`, x ↦ ι(Φ_τ(x̄)). So g acts through its
conjugate, the inverse transpose of g, and the gauge is the multiplicative form of the least
valuation of a coordinate. -/
def weylGauge (g : Gf E n) (ξ : WeylIndexFamily (fun _ : InfinitePlace E ↦ n) κ → ℂ) : ℝ :=
  ‖weylRep κ e (fun τ ↦
    GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) g⁻¹.val) *ᵥ ιₚ ∘ ξ‖

variable (n p)

/-- The subgroup of finite adelic unitary points whose components at all primes above p are
integral invertible matrices. -/
abbrev integralAbove {E : Type} (n : Type) [Field E] [NumberField E] [IsCMField E] [Fintype n]
    [DecidableEq n] (p : ℕ) : Subgroup (Gf E n) := localLevel n {w : FinPlace E | ↑p ∈ w.asIdeal}

end AlgFormDefs

/-!
## From algebraic forms to functions on the adelic points

* `New.algFormCoeff`, `New.ofAlgForm`: the scalar function on all adelic points of a form.
-/

section AlgebraicFormDefs

open NumberField

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  (l : InfinitePlace E → n → ℤ) {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ}

/-- For a linear functional L on vectors of weight (κ, e), the linear map sending an algebraic form
φ to the function g ↦ L(ρ(g_∞⁻¹) φ(g_f)) on G, with ρ = `New.conjWeylRep`. -/
@[simps! -isSimp apply]
noncomputable def algFormCoeff (s : n → ℤˣ) (L : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) :
    AlgForm (E := E) n κ e →ₗ[ℂ] G E s → ℂ :=
  LinearMap.pi fun g ↦ L ∘ₗ conjWeylRep κ e g.1⁻¹ ∘ₗ
    LinearMap.domRestrict (LinearMap.proj g.2) (AlgForm n κ e)

/-- The linear map φ ↦ F_φ from algebraic forms of weight (κ, e) to functions on G, F_φ(g) = ⟨v⁺,
ρ(g_∞⁻¹) φ(g_f)⟩, with v⁺ = `New.highestVector` for l, a vector built from the decreasing order of
the entries of l (a unit vector for ⟨·,·⟩ = `New.gramForm` when each l w is injective). -/
noncomputable abbrev ofAlgForm (s : n → ℤˣ) : ↥(AlgForm n κ e) →ₗ[ℂ] G E s → ℂ :=
  algFormCoeff (E := E) (e := e) s (gramForm (n := n) (highestVector κ l))

lemma Space.IsStd.eq_stdSpace (V : Space E n 1) [IsStd V] : V = stdSpace E n := ext point_eq_one

/-- Induction principle for standard spaces (all signs `1`, point the identity matrix). To prove a
statement about every standard space with its proof of standardness, it suffices to prove it for
`New.stdSpace` with signs `1`. -/
@[elab_as_elim, induction_eliminator]
lemma Space.IsStd.std_induction {motive : ∀ (s : n → ℤˣ) (V : Space E n s), V.IsStd → Prop}
    (h : motive 1 (stdSpace E n) ⟨rfl, rfl⟩) {s : n → ℤˣ} {V : Space E n s} (hV : V.IsStd) :
    motive s V hV := by
  obtain rfl : s = 1 := hV.signs_eq_one
  obtain rfl : V = stdSpace E n := eq_stdSpace V
  exact h

end AlgebraicFormDefs

/-!
## The invariant pairing of smooth algebraic forms

Here V is a definite hermitian space (`New.Space` with all signs 1), and Γ is the image of the
rational unitary group in G_f under `New.Space.embFin`. A weight κ of type `New.Weight` is a pair:
κ.1 counts the columns of each height and κ.2 gives the powers of the determinant.

* `New.Space.forms`: the functions on G_f fixed by an open subgroup under right translation that
  transform on the left by the weight κ representation `New.Space.weightRep`.
* `New.Space.formTranslation`: the action of G_f on forms by right translation.

`New.classIntegral` is the integral over Γ\G_f normalised by vol K₀ = 1, with K₀ = `New.stdLevel`.
-/

section SmoothFormPairing

variable {E : Type} {n : Type} [Field E] [CMType E] [Fintype n]
  [DecidableEq n] (V : Space E n 1) (κ : Weight E)

/-- Algebraic modular forms of weight κ on a definite space V: functions f on G_f with open
right stabiliser and f(γg) = ρ_κ(γ)f(g) for rational γ, ρ_κ = `New.Space.weightRep`. -/
def Space.forms : Submodule ℂ (Gf E n → WeylIndex n κ.1 → ℂ) :=
  SmoothForm V.embFin (V.weightRep κ.1 κ.2)

/-- The representation of the finite adelic unitary group on forms of weight κ on V by right
translation. -/
@[simps! -fullyApplied apply_apply_coe]
def Space.formTranslation : Representation ℂ (Gf E n) (V.forms κ) :=
  (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)).subrepresentation (V.forms κ) fun a φ hφ ↦
    (smoothFormRep V.embFin (weightRep κ.1 κ.2 V) a ⟨φ, hφ⟩).property

variable {V κ} {σ : ℂ →+* ℂ} {B : (WeylIndex n κ.1 → ℂ) →ₛₗ[σ] (WeylIndex n κ.1 → ℂ) →ₗ[ℂ] ℂ}

/-- For forms φ and ψ of weight κ = (κ.1, κ.2) (column counts and determinant powers) on the
definite space V, and B invariant under `New.Space.weightRep`, the function g ↦ B(φ(g), ψ(g)) is
left invariant under the group `V.Γf` of rational points and fixed by an open subgroup under right
translation, so that `New.classIntegral` applies to it. -/
@[local simp]
lemma pairing_mem_smoothInvariants
    (hB : ∀ (γ : U V.J) (v v' : WeylIndex n κ.1 → ℂ),
      B (V.weightRep κ.1 κ.2 γ v) (V.weightRep κ.1 κ.2 γ v') = B v v')
    (φ ψ : V.forms κ) :
    (fun g : Gf E n ↦ B (φ.val g) (ψ.val g)) ∈ smoothInvariants V.Γf := by
  obtain ⟨φ, hφ_smooth, hφ_equivariant⟩ := φ
  obtain ⟨ψ, hψ_smooth, hψ_equivariant⟩ := ψ
  refine ⟨Set.forall_mem_range.2 ?_, ?_⟩
  · -- Both forms transform under `V.weightRep`, which preserves `B`.
    show ∀ (γ : U V.J) (g : Gf E n), B (φ (V.embFin γ * g)) (ψ (V.embFin γ * g)) = B (φ g) (ψ g)
    simp [hφ_equivariant _, hψ_equivariant _, hB]
  · -- The pairing is fixed by every translation that fixes both forms.
    have h_open : (rightStabilizer φ ⊓ rightStabilizer ψ).IsOpen := .inter hφ_smooth hψ_smooth
    exact Subgroup.isOpen_mono (fun k hk g ↦ by simp only [hk.1 g, hk.2 g]) h_open

variable (B) in
/-- For a σ-sesquilinear B invariant under the weight κ action of U(J)(E), this is the pairing (φ,
φ') ↦ ∫ B(φ(g), φ'(g)) dg of forms on the definite space V, over Γ\G_f with vol K₀ = 1. -/
def smoothPairing
    (hB : ∀ (γ : U V.J) (v v' : WeylIndex n κ.1 → ℂ),
      B (V.weightRep κ.1 κ.2 γ v) (V.weightRep κ.1 κ.2 γ v') = B v v') :
    V.forms κ →ₛₗ[σ] V.forms κ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ σ (RingHom.id ℂ)
    (fun φ φ' ↦ classIntegral V.Γf (stdLevel E n) fun g ↦ B (φ.val g) (φ'.val g))
    -- The integral is additive on smooth invariant functions, so this is σ-sesquilinear.
    (fun φ₁ φ₂ ψ ↦ by simp [classIntegral_add, ← Pi.add_def, hB])
    (fun c φ ψ ↦ by simp)
    (fun φ ψ₁ ψ₂ ↦ by simp [classIntegral_add, ← Pi.add_def, hB])
    (fun c φ ψ ↦ by simp)

/-- The value of `New.smoothPairing` at two forms is the integral of their pointwise pairing. -/
lemma smoothPairing_apply
    (hB : ∀ (γ : U V.J) (v v' : WeylIndex n κ.1 → ℂ),
      B (V.weightRep κ.1 κ.2 γ v) (V.weightRep κ.1 κ.2 γ v') = B v v')
    (φ φ' : V.forms κ) :
    smoothPairing B hB φ φ' =
      classIntegral V.Γf (stdLevel E n) fun g : Gf E n ↦ B (φ.val g) (φ'.val g) :=
  rfl

/-- The pairing `New.smoothPairing` of forms of weight κ on the definite space V, by a form `B`
invariant under `New.Space.weightRep`, is unchanged when both forms are translated on the right by
the same finite adelic point `a`. -/
lemma smoothPairing_formTranslation
    (hB : ∀ (γ : U V.J) (v v' : WeylIndex n κ.1 → ℂ),
      B (V.weightRep κ.1 κ.2 γ v) (V.weightRep κ.1 κ.2 γ v') = B v v')
    (a : Gf E n) (φ φ' : V.forms κ) :
    smoothPairing B hB (V.formTranslation κ a φ) (V.formTranslation κ a φ') =
      smoothPairing B hB φ φ' := by
  -- The integral over Γ\G_f does not change under right translation of the integrand.
  rw [smoothPairing_apply, smoothPairing_apply]
  exact classIntegral_map_mul_right (.id ℂ) a (pairing_mem_smoothInvariants hB φ φ') fun g ↦ by simp

end SmoothFormPairing

end New

/-!
## Harish-Chandra parameters, formal degrees and dimension

Facts on `New.IsHCParam κ e l`: the vector `l` lists, at each place and in some order, twice the
Harish-Chandra parameter `λ + ρ` of the weight `(κ, e)` of the compact group `U(n)`.
`New.hcParameter` is that vector as a decreasing sequence, and `New.decreasingPosition` is the
position of an index in it.
-/

section WeightParameter

open MeasureTheory Complex ComplexConjugate Finset Fintype

namespace New

variable {Φ n : Type} [Fintype Φ] [Fintype n]
  {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {N : ℕ} {l : Φ → HCParam (n := n) 1}

/-! ### Existence of parameters, and cyclicity of the highest vector -/

lemma hcParameter_strictAnti {w : Φ} : StrictAnti (hcParameter κ e N w) :=
  strictAnti_nat_of_succ_lt (by grind [hcParameter])

/-- Index the entries of the decreasing sequence `hcParameter κ e (card n) w` by `n` through the
enumeration `Fintype.equivFin n`. The resulting vector satisfies `IsHCParam κ e`. -/
lemma isHCParam_hcParameter [DecidableEq Φ] (n : Type) [Fintype n] (κ : Φ → ℕ → ℕ) (e : Φ → ℤ) :
    IsHCParam κ e fun (w : Φ) (i : n) ↦
      hcParameter κ e (Fintype.card n) w (Fintype.equivFin n i) := by
  simp [IsHCParam, Function.Injective, hcParameter_strictAnti.injective.eq_iff, Fin.val_inj]

/-- Let L be a sequence of integers with L(p) − L(p+1) = 2κ_w(p+1) + 2 whenever p + 1 < N. If L
agrees with `New.hcParameter κ e N w` at one index q < N, then it agrees with it at every p < N.
That sequence is the decreasing parameter for rank N, and it has these same steps. -/
lemma hcParameter_eq_of_steps (w : Φ) (L : ℕ → ℤ)
    (h_step : ∀ p : ℕ, p + 1 < N → L p = L (p + 1) + 2 * κ w (p + 1) + 2) {q : ℕ} (hq : q < N)
    (h_agree : L q = hcParameter κ e N w q) :
    ∀ p : ℕ, p < N → hcParameter κ e N w p = L p := by
  -- `L` and `hcParameter κ e N w` have the same steps, so their difference is constant; it is `0`
  -- at `q`.
  have diff_const (p : ℕ) (hp : p < N) :
      L p - hcParameter κ e N w p = L 0 - hcParameter κ e N w 0 := by
    induction p with
    | zero => rfl
    | succ p ih =>
      have h_row : diagramWeight (fun _ ↦ N) κ (w, p) =
          diagramWeight (fun _ ↦ N) κ (w, p + 1) + κ w (p + 1) := by
        rw [GL.diagramWeight_eq_succ_add, ite_eq_left hp]
      have h_param : hcParameter κ e N w p = hcParameter κ e N w (p + 1) + 2 * κ w (p + 1) + 2 := by
        grind [hcParameter]
      linarith [ih (Nat.lt_of_succ_lt hp), h_step p hp]
  intro p hp
  linarith [diff_const p hp, diff_const q hq]

variable [DecidableEq Φ]

/-- Let each `l w` be injective, v⁺ = `New.highestVector`, ρ = `New.conjWeylRep` and
⟨·,·⟩ = `New.gramForm`. If f(ρ(x) v⁺) ⟨v⁺, ρ(x⁻¹) u⟩ = 0 for all x in the compact group (`USign 1`
at each place), then f(u) = 0. -/
lemma apply_eq_zero_of_mul_gramForm_highestVector [DecidableEq n]
    (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ)
    (f : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) (u : WeylIndex n κ → ℂ)
    (h_zero : ∀ x : Φ → USign 1, f (conjWeylRep κ e (s := 1) x (highestVector κ l)) *
      gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x⁻¹ u) = 0) :
    f u = 0 := by
  -- The highest vector is a unit vector, so by Schur orthogonality the mean of the product is
  -- `(dim ρ)⁻¹ f u`.
  have h_schur : ∫ x : Φ → USign 1, f (conjWeylRep κ e (s := 1) x (highestVector κ l)) *
      gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x⁻¹ u) =
        (card (WeylIndex n κ) : ℂ)⁻¹ * f u := by
    rw [schur_orthogonality, gramForm_highestVector_self hl, mul_one]
  simp only [h_zero, integral_zero] at h_schur
  exact (mul_eq_zero_iff_left (inv_ne_zero (Nat.cast_ne_zero.2 card_ne_zero))).1 h_schur.symm

/-- Let each `l w` be injective, so that it orders the indices and gives the vector
`v⁺ = New.highestVector κ l`. A vector `u` is zero if all its translates ρ(x)u are orthogonal to
v⁺ for the form `New.gramForm`. Here x runs over the compact group (`USign 1` at each place) and
ρ = `New.conjWeylRep` is its representation of weight (κ, e). -/
lemma eq_zero_of_forall_gramForm_translate_eq_zero [DecidableEq n]
    (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ) (u : WeylIndex n κ → ℂ)
    (h_orth : ∀ x : Φ → USign 1, gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x u) = 0) :
    u = 0 := by
  funext i
  exact apply_eq_zero_of_mul_gramForm_highestVector hl e (LinearMap.proj i) u (by simp [h_orth])

/-- Let each `l w` be injective, and let v⁺ = `New.highestVector κ l`. A linear form that kills all
translates ρ(x)v⁺ under the compact group (`USign 1` at each place, acting in weight (κ, e) by
ρ = `New.conjWeylRep`) is zero. -/
lemma eq_zero_of_forall_map_translate_highestVector_eq_zero [DecidableEq n]
    (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ) (f : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ)
    (hf : ∀ x : Φ → USign 1, f (conjWeylRep κ e (s := 1) x (highestVector κ l)) = 0) :
    f = 0 := by
  exact LinearMap.ext fun u ↦ apply_eq_zero_of_mul_gramForm_highestVector hl e f u (by simp [hf])

/-- Let each `l w` be injective, and let v⁺ = `New.highestVector κ l`. The translates ρ(x)v⁺ under
the compact group (`USign 1` at each place, acting in weight (κ, e) by ρ = `New.conjWeylRep`) span
the space of coordinate vectors. -/
lemma span_translate_highestVector_eq_top [DecidableEq n]
    (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ) :
    Submodule.span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦
      conjWeylRep κ e x (highestVector κ l)) = ⊤ := by
  -- A proper subspace lies in the kernel of a nonzero linear form.
  by_contra h_proper
  obtain ⟨f, hf_ne, hf_ker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h_proper)
  exact hf_ne <| eq_zero_of_forall_map_translate_highestVector_eq_zero hl e f
    fun x ↦ hf_ker (Submodule.subset_span ⟨x, rfl⟩)

/-- Let each `l w` be injective, and let v⁺ = `New.highestVector κ l`. The linear forms
u ↦ ⟨v⁺, ρ(x)u⟩ span the dual space. Here ⟨·,·⟩ = `New.gramForm`, and x runs over the compact
group (`USign 1` at each place), acting in weight (κ, e) by ρ = `New.conjWeylRep`. -/
lemma span_gramForm_highestVector_comp_eq_top [DecidableEq n]
    (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ) :
    Submodule.span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦
      gramForm (highestVector κ l) ∘ₗ conjWeylRep κ e x) = ⊤ := by
  -- The common kernel of these forms is zero, so it lies in the kernel of every linear form `f`.
  refine Submodule.eq_top_iff'.2 fun f ↦
    FiniteDimensional.mem_span_of_iInf_ker_le_ker fun u hu ↦ ?_
  have h_orth (x : Φ → USign (1 : n → ℤˣ)) :
      gramForm (highestVector κ l) (conjWeylRep κ e x u) = 0 := (Submodule.mem_iInf _).1 hu x
  simp [eq_zero_of_forall_gramForm_translate_eq_zero hl e u h_orth]

/-- Let each `l w` be injective. For any determinant twist `e`, the highest vector
v⁺ = `New.highestVector κ l` and its dual ⟨v⁺, ·⟩ for `New.gramForm` are cyclic under the compact
group (`USign 1` at each place, acting by ρ = `New.conjWeylRep`): the vectors ρ(x)v⁺ span the
representation, and the linear forms u ↦ ⟨v⁺, ρ(x)u⟩ span its dual. Both facts are consequences of
the irreducibility of the Schur module. -/
lemma highestVector_cyclic [DecidableEq n] (hl : ∀ w : Φ, (l w).Injective) (e : Φ → ℤ) :
    Submodule.span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦
      conjWeylRep κ e x (highestVector κ l)) = ⊤ ∧
    Submodule.span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦
      gramForm (highestVector κ l) ∘ₗ conjWeylRep κ e x) = ⊤ :=
  ⟨span_translate_highestVector_eq_top hl e, span_gramForm_highestVector_comp_eq_top hl e⟩

/-! ### Positions in the decreasing order -/

/-- For an injective integer vector `a` indexed by `n`, every position `q < card n` in the
decreasing order of `a` is taken by some index. Here `decreasingPosition a i` counts the indices k
with a i < a k, so positions start at 0. -/
lemma exists_decreasingPosition_eq_of_injective {a : n → ℤ} (ha : a.Injective) {q : ℕ}
    (hq : q < Fintype.card n) : ∃ i : n, decreasingPosition a i = q := by
  obtain ⟨f, hf⟩ := exists_equiv_decreasingPosition ha
  exact ⟨f.symm ⟨q, hq⟩, by simp [(hf _).1]⟩

/-- If `x < a i`, then the number of entries of `a` that exceed `x` is larger than the position of
`i` in the decreasing order of `a`. -/
lemma decreasingPosition_lt_card_of_lt {a : n → ℤ} {i : n} {x : ℤ} (hx : x < a i) :
    decreasingPosition a i < #{k : n | x < a k} := by
  -- The indices `k` with `a i < a k` satisfy `x < a k`, and so does `i`.
  refine card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨i, by simp [hx], by simp⟩)
  exact monotone_filter_right _ fun k _ hk ↦ hx.trans hk

/-! ### Consequences of `New.IsHCParam` -/

section

omit [DecidableEq Φ]

lemma IsHCParam.injective (h : IsHCParam κ e l) (w : Φ) : (l w).Injective := (h w).1

/-- Here `hcParameter κ e N w p` = 2μ_p + N − 1 − 2p is entry p of twice μ + ρ in rank N, for the
highest weight μ_p = e_w + Σ_{p<h<N} κ_w(h) at the place `w`. If `l` lists twice the Harish-Chandra
parameter of `(κ, e)` in some order, then `l w i` is the entry of `hcParameter` at the position of
`i` in the decreasing order of `l w`, that is, the number of `j` with `l w i < l w j`. -/
lemma IsHCParam.eq_hcParameter (h : IsHCParam κ e l) (w : Φ) (i : n) :
    l w i = hcParameter κ e (Fintype.card n) w (decreasingPosition (l w) i) := by
  -- Write `l w j` as entry `v j` of the strictly decreasing sequence `hcParameter`. Then `v` is a
  -- bijection onto `Fin (card n)` that reverses the order, so `v i` is the position
  -- `decreasingPosition` of `i`.
  choose v hv using show ∀ j : n, ∃ p : Fin (card n), l w j = hcParameter κ e (card n) w p by
    simpa [Fin.exists_iff] using (h w).2
  have hv_inj : v.Injective := fun j k hjk ↦ h.injective w (by rw [hv j, hv k, hjk])
  have hv_bij : v.Bijective := (bijective_iff_injective_and_card v).2 ⟨hv_inj, by simp⟩
  have h_position : decreasingPosition (l w) i = v i := by
    rw [decreasingPosition, ← Fin.card_Iio (v i)]
    exact card_bijective v hv_bij (by simp [hv, hcParameter_strictAnti.lt_iff_gt])
  rw [h_position, hv]

/-- For a parameter `l` of `(κ, e)`, every position q < |n| is taken: some index i is at position q
in the decreasing order of `l w`, its entry is entry q of the parameter, and for each x below that
entry more than q entries of `l w` exceed x. -/
lemma IsHCParam.exists_decreasingPosition_eq (h : IsHCParam κ e l) (w : Φ) {q : ℕ}
    (hq : q < Fintype.card n) :
    ∃ i : n,
      decreasingPosition (l w) i = q ∧
      l w i = hcParameter κ e (Fintype.card n) w q ∧
      ∀ x : ℤ, x < l w i → q < #{k : n | x < l w k} := by
  obtain ⟨i, rfl⟩ := exists_decreasingPosition_eq_of_injective (h.injective w) hq
  exact ⟨i, rfl, h.eq_hcParameter w i, fun x hx ↦ decreasingPosition_lt_card_of_lt hx⟩

/-- The entries of `l w` are the first `card n` entries of the decreasing parameter. -/
lemma IsHCParam.image_eq (h : IsHCParam κ e l) (w : Φ) :
    univ.image (l w) = (range (Fintype.card n)).image (hcParameter κ e (Fintype.card n) w) := by
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  refine ⟨fun ⟨i, hi⟩ ↦ by simpa only [← hi, eq_comm] using (h w).2 i, fun ⟨p, hp, hy⟩ ↦ ?_⟩
  obtain ⟨i, -, hi, -⟩ := h.exists_decreasingPosition_eq w hp
  exact ⟨i, hi.trans hy⟩

/-- For a parameter `l` of `(κ, e)` and every natural number `c`, the vector `l w` satisfies
`New.HCParam.HasGap c`: its entries are distinct and of the parity of `card n - 1`, and the gap
condition is empty as all signs are `1`. -/
lemma IsHCParam.hasGap (h : IsHCParam κ e l) (w : Φ) (c : ℕ) : (l w).HasGap c where
  injective := h.injective w
  parity i := by grind [h.eq_hcParameter, hcParameter]
  gap _ _ := nofun

/-- Let `κ` give column multiplicities at each place w (κ_w(h) columns of height h) and let `e` give
an integer e_w at each w, and suppose l is twice the Harish-Chandra parameter of the weight (κ, e).
Then for signs all 1, the entry at i of `New.HCParam.lowestKType` of l_w equals e_w + Σ_{p<h<|n|}
κ_w(h), where p is the number of j with l_w(j) > l_w(i). Here `New.HCParam.lowestKType` is the
highest weight of the lowest K-type, with K = U(n). The sum is `New.diagramWeight` at (w, p), with
`rankAt` giving the rank |n| at every place. -/
lemma IsHCParam.lowestKType_eq (h : IsHCParam κ e l) (w : Φ) (i : n) :
    (l w).lowestKType i =
      e w + diagramWeight (rankAt fun _ : Φ ↦ n) κ (w, decreasingPosition (l w) i) := by
  -- With `p = decreasingPosition (l w) i` we have `2ρ_i = card n - 1 - 2 * p` and
  -- `l w i = 2λ_p + 2ρ_i`, so `(l w i + 2ρ_i) / 2 - 2ρ_i = λ_p`.
  let twoRho_i : ℤ := #{j : n | l w j < l w i} - #{j : n | l w i < l w j}
  have h_lowest : (l w).lowestKType i = (l w i + twoRho_i) / 2 - twoRho_i := by
    simp [HCParam.lowestKType, paramAddRho, twoRho, twoRho_i]
  have h_count : #{j : n | l w j < l w i} + #{j : n | l w i < l w j} + 1 = card n :=
    card_lt_add_card_gt_add_one (h.injective w) i
  grind [h.eq_hcParameter w i, hcParameter, decreasingPosition]

end

variable [DecidableEq n]

/-- Let `κ` give column multiplicities at each place w (κ_w(h) columns of height h) and let `e` give
an integer e_w at each w; together (κ, e) is the weight whose entry at position p of place w is
e_w + Σ_{p<h<|n|} κ_w(h). Suppose l is twice the Harish-Chandra parameter of (κ, e)
(`New.IsHCParam`), and take x in the product over w of U(n) = U(diag 1). Then the matrix coefficient
⟨v⁺, ρ(x)v⁺⟩ at the highest vector v⁺ = `New.highestVector` is ∏_w conj ψ_{l_w}(x_w), where
ρ = `New.conjWeylRep` is the representation on coordinate vectors of weight (κ, e),
ψ = `New.HCParam.dsCoeff` and ⟨·,·⟩ = `New.gramForm`. -/
lemma IsHCParam.gramForm_conjWeylRep_eq_dsCoeff (h : IsHCParam κ e l) (x : Φ → USign 1) :
    gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x (highestVector κ l)) =
      ∏ w : Φ, conj ((l w).dsCoeff (x w)) := by
  -- `f w` orders the indices by decreasing `l w`, and `y` is the entrywise conjugate of `x`.
  choose f hf using fun w : Φ ↦ exists_equiv_decreasingPosition (h.injective w)
  let y (w : Φ) : GL n ℂ := Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (x w)
  -- On the compact group, `conj dsCoeff` is `weightMinors` for the highest weight, taken at `y`.
  have h_psi (w : Φ) : conj ((l w).dsCoeff (x w)) =
      weightMinors (fun i : n ↦ e w + diagramWeight (rankAt fun _ : Φ ↦ n) κ (w, f w i)) (y w) := by
    have h_weight : (l w).lowestKType = fun i : n ↦
        e w + diagramWeight (rankAt fun _ : Φ ↦ n) κ (w, f w i) := by
      simp [funext (h.lowestKType_eq w), hf]
    have h_conj : ((x w : GL n ℂ) : Matrix n n ℂ).conjTranspose.transpose = y w := rfl
    rw [dsCoeff_of_mem_maxCompactU (h.hasGap w 0) (by simp [mem_maxCompactU]), h_weight,
      conj_weightMinors, ← weightMinors_transpose, h_conj]
  -- The coefficient is the product of these minors, as `conjWeylRep` acts by `weylRep` at `y`.
  have h_act (v : WeylIndex n κ → ℂ) :
      conjWeylRep κ e (s := 1) x v = (weylRep κ e y).mulVec v := rfl
  rw [gramForm_apply, star_highestVector, h_act]
  simp only [h_psi, highestVector, hf]
  exact weylRep_coeff_eq_prod_weightMinors (n := fun _ : Φ ↦ n) f y

/-- If l is twice the Harish-Chandra parameter of (κ, e), the product over w of the formal degrees
`New.HCParam.formalDegree` of l_w for the compact group U(n) equals the dimension of the
representation of weight (κ, e), the number of elements of its basis `New.WeylIndex`. The formal
degree is the reciprocal of the mean of the squared modulus of `New.HCParam.dsCoeff`.

This is a case of the Schur orthogonality relations, for one matrix coefficient of the
representation of weight (κ, e) of a product of compact groups U(n). -/
lemma IsHCParam.prod_formalDegree (h : IsHCParam κ e l) :
    ∏ w : Φ, (l w).formalDegree = Fintype.card (WeylIndex n κ) := by
  -- Schur orthogonality at the highest vector, a unit vector: the mean of the squared modulus of
  -- its matrix coefficient is the reciprocal of the dimension. The coefficient is the conjugate of
  -- `∏ w, (l w).dsCoeff`, and `dsCoeff` at `x⁻¹` is the conjugate of `dsCoeff` at `x`.
  have h_coeff_inv (x : Φ → USign 1) :
      gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x⁻¹ (highestVector κ l)) =
        ∏ w : Φ, (l w).dsCoeff (x w) := by
    simp only [h.gramForm_conjWeylRep_eq_dsCoeff, Pi.inv_apply, dsCoeff_inv (h.hasGap _ 0),
      conj_conj]
  have h_mean : ∫ x : Φ → USign (1 : n → ℤˣ), ∏ w : Φ, (‖(l w).dsCoeff (x w).val‖ : ℂ) ^ 2 =
      (card (WeylIndex n κ) : ℂ)⁻¹ := by
    have h_schur : ∫ x : Φ → USign (1 : n → ℤˣ),
        gramForm (highestVector κ l) (conjWeylRep κ e x (highestVector κ l)) *
          gramForm (highestVector κ l) (conjWeylRep κ e x⁻¹ (highestVector κ l)) =
          (card (WeylIndex n κ) : ℂ)⁻¹ := by
      simp [schur_orthogonality, gramForm_highestVector_self h.injective]
    simpa [h_coeff_inv, h.gramForm_conjWeylRep_eq_dsCoeff, ← prod_mul_distrib, conj_mul'] using
      h_schur
  -- The integral splits over the places, and each factor is the reciprocal of `formalDegree`.
  have h_split : ((∏ w : Φ, (l w).formalDegree⁻¹ : ℝ) : ℂ) =
      ∫ x : Φ → USign (1 : n → ℤˣ), ∏ w : Φ, (‖(l w).dsCoeff (x w).val‖ : ℂ) ^ 2 := by
    simp [formalDegree, ← integral_fintype_prod_eq_prod, ← integral_complex_ofReal, volume_pi]
  refine inv_injective (ofReal_injective ?_)
  simpa [← prod_inv_distrib] using h_split.trans h_mean

end New

end WeightParameter

end
