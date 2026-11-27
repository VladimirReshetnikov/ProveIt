import Lib.Adelic.Landherr
import Lib.Adelic.TraceFormula.OrbitalUnfolding
import Lib.DiscreteSeries.Character.FormalDegree

/-!
# Comparison of traces of operators on forms for different spaces and signs

A simple trace formula for the unitary group of a hermitian space `V`, with terms sorted by the
characteristic polynomials `R` of rational points. The test function is `e ⊗ φ`, with `e` a cusp
kernel on the real group and `φ` locally constant of compact support on the finite adelic group.

This file proves the Selberg principle: orbital integrals of an irreducible `R` with a root off
the unit circle vanish. For `R` with all roots on the unit circle, it splits orbital integrals into
real and finite factors and matches the classes of different signs. It concludes that the trace on
forms depends neither on the space nor on its signs.

## Main definitions and results

* `New.Space.orbitalIntegral_eq_zero`: the orbital integral is `0` if `R` is irreducible with a root
  off the unit circle.
* `New.Space.exists_geometricSide_singleton_eq`: if `R` is irreducible with all roots on the unit
  circle, `E` contains the 5040th roots of unity and has an even number of infinite places, and the
  parameter has a large gap, its term is a product of characters of the compact unitary group times
  a number that depends only on `R` and `φ`.
* `New.trace_comparison`: let `E` contain the 5040th roots of unity and have an even number of
  infinite places, let `n ≥ 2`, and let the parameter have a large gap. If `φ` is cuspidal at a
  split place and, at a place `w'`, the elements of its support are integral with `0` a simple root
  of the characteristic polynomial modulo `w'`, the reducible `R` contribute nothing, so the trace
  depends neither on the space nor on its signs.

Notions from other files:
* `New.Space E n s`: a hermitian form `J` over `E` with an adelic frame `x` in which it is `diag s`
  at infinity and `1` at the finite places. `V.ratEmbed` embeds `U(J)(E)` in `G = G_∞ × G_f` with
  image `Γ = V.Γ`, and `V.quotMeasure` integrates over `[G] = Γ \ G`.
* `New.IsCuspKernel B e`: `e` is a minimal convolution idempotent on `G_∞` with moment of order
  `B + 1` and decay of order `B`, and `α ⋆ e = e` for some continuous compactly supported `α`.
* `V.polyTerm k φ S γ x`: the value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of `γ`
  lies in `S`, and `0` otherwise.
* `V.formRep e`: the action of `G_f` on the forms of type `e`, which for integrable `e` are the
  bounded automorphic functions on `G` fixed by right convolution with `e`; a level `K` is an open
  subgroup of the standard compact subgroup.
* `New.Space.orbitalIntegral` (in `Lib.Adelic.TraceFormula.OrbitalUnfolding`): the orbital integral
  `I_γ`, the integral of the term of `γ` over `G` modulo the rational centraliser of `γ`.

## Relation to the literature

Comparison of simple trace formulas for unitary groups that differ only at real places. Here
integrable idempotent kernels of very regular discrete series replace pseudo-coefficients, and the
CM field contains the 5040th roots of unity and has an even number of infinite places. There is no
truncation and no endoscopy. Source: Labesse, Changement de base CM et séries discrètes (2011),
Thms 5.4, 5.5 and their proofs; Arthur and Clozel (1989), ch. 1, Lemmas 2.4-2.6; integrable test
functions as in Knightly and Li, Traces of Hecke operators (2006); for the simple trace formula
with a cuspidal component, Flicker and Kazhdan (1988) and Harris and Labesse (2004), Prop. 1.10.5.

Selberg principle that orbital integrals of an idempotent vanish off the elliptic set. Here the
idempotent is a minimal convolution idempotent with polynomial decay on a product of groups
U(p,q), placed inside the adelic orbital integral of a rational point with irreducible
characteristic polynomial. If some eigenvalue has absolute value other than 1, this integral is
zero. Source: Harish-Chandra, Discrete series II, Acta Math. 116 (1966), Thm 11; Blanc and
Brylinski, Cyclic homology and the Selberg principle, J. Funct. Anal. 109 (1992); Hochs and Wang,
Orbital integrals and K-theory classes (2019), Cor 4.8.
-/

noncomputable section

open MeasureTheory Fintype

open NumberField Measure Matrix Polynomial Module Subgroup Complex MulAction New.Variety Finset
  Equiv Real ConjAct ENNReal

open scoped Norms.L2Operator InnerProductSpace ComplexOrder

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

namespace Space

variable {s : n → ℤˣ} (V : Space E n s) {B : ℕ} {k e : GInf E s → ℂ}

/-! ### The Selberg principle -/

/-- The trace property for the triple kernel of `e ⊗ φ` at the rational point `γ`. Let `a` be a
weight on triples that is invariant under left translation by the rational centraliser of `γ`, and
let `b` be `a` composed with the rotation of triples. Then the kernel has the same integral against
`a` and against `b`, if both converge. -/
lemma integral_mul_tripleKernel_tripleRotate (φ : TestFunction (Gf E n)) (he : Measurable e)
    {γ : U V.J} {a b : G E s × GInf E s × GInf E s → ℝ} (ha_meas : Measurable a)
    (ha : Integrable (fun p : G E s × GInf E s × GInf E s ↦ a p * V.tripleKernel e φ γ p)
      (V.tripleMeasure γ))
    (hb : Integrable (fun p : G E s × GInf E s × GInf E s ↦ b p * V.tripleKernel e φ γ p)
      (V.tripleMeasure γ))
    (hab : ∀ p : G E s × GInf E s × GInf E s, a (V.tripleRotate γ p) = b p)
    (ha_inv : ∀ t : U V.J, Commute γ t → ∀ (x : G E s) (q : GInf E s × GInf E s),
      a (V.ratEmbed t * x, q) = a (x, q)) :
    ∫ p : G E s × GInf E s × GInf E s, b p * V.tripleKernel e φ γ p ∂V.tripleMeasure γ =
      ∫ p : G E s × GInf E s × GInf E s, a p * V.tripleKernel e φ γ p ∂V.tripleMeasure γ := by
  let f (p : G E s × GInf E s × GInf E s) : ℂ := a p * V.tripleKernel e φ γ p
  have h_comp (p : G E s × GInf E s × GInf E s) :
      f (V.tripleRotate γ p) = b p * V.tripleKernel e φ γ p := by
    simp only [f, hab, V.tripleKernel_tripleRotate]
  simpa only [h_comp] using V.integral_comp_tripleRotate (f := f) (by fun_prop) ha
    (by simpa only [h_comp] using hb)
    fun t ht x q ↦ by simp only [f, ha_inv t ht, V.tripleKernel_ratEmbed_mul φ ht]

/-- Let `V` be a hermitian space with a frame, and let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`:
a minimal idempotent with `‖x‖^(B+1) e(x)` integrable, `‖x‖^B e(x)` bounded, and `α ⋆ e = e` for
some continuous compactly supported `α`. Let the rational point `γ` have an irreducible
characteristic polynomial, and let `H` be a measurable function on the real group that moves by at
most `∏_w ‖b_w‖` under right multiplication by `b`. If the real part of `γ` shifts `H` by `ℓ` on the
left and every rational point that commutes with `γ` shifts it by a constant, then `ℓ` times the
orbital integral of `e ⊗ φ` at `γ` (over `G` modulo the rational centraliser of `γ`) vanishes. -/
lemma mul_orbitalIntegral_eq_zero [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {γ : U V.J}
    (hγ : Irreducible (γ : GL n E).val.charpoly) {H : GInf E s → ℝ} {ℓ : ℝ} (hH : Measurable H)
    (h_lip : ∀ a b : GInf E s, |H (a * b) - H a| ≤ ∏ w : InfinitePlace E, ‖(b w : Matrix n n ℂ)‖)
    (h_shift : ∀ y : GInf E s, H ((V.ratEmbed γ).1 * y) = ℓ + H y)
    (h_cent : ∀ t : U V.J, Commute γ t →
      ∃ r : ℝ, ∀ y : GInf E s, H ((V.ratEmbed t).1 * y) = r + H y) :
    ℓ * V.orbitalIntegral e φ γ = 0 := by
  -- Write `I_γ = tr (p p p γ)` for the projection `p(a, b) = e(a⁻¹ b)`; let `∂` multiply a kernel
  -- by `H b - H a`. On triples `(x, y, u)` the weights `a₁`, `a₂`, `a₃` are the increments of `H`
  -- along `x, x y, x y u, γ x`; they give `∂p p p`, `p ∂p p` and `p p ∂p`.
  have h_meas : Measurable e := he.continuous.measurable
  let P : G E s × GInf E s × GInf E s → ℂ := V.tripleKernel e φ γ
  let m : Measure (G E s × GInf E s × GInf E s) := V.tripleMeasure γ
  let a₁ (p : G E s × GInf E s × GInf E s) : ℝ := H (p.1.1 * p.2.1) - H p.1.1
  let a₂ (p : G E s × GInf E s × GInf E s) : ℝ := H (p.1.1 * p.2.1 * p.2.2) - H (p.1.1 * p.2.1)
  let a₃ (p : G E s × GInf E s × GInf E s) : ℝ := ℓ + H p.1.1 - H (p.1.1 * p.2.1 * p.2.2)
  have h_sum (p : G E s × GInf E s × GInf E s) :
      ℓ * P p = a₁ p * P p + a₂ p * P p + a₃ p * P p := by
    simp [a₁, a₂, a₃, ← add_mul]
  have one_le (y : GInf E s) : 1 ≤ ∏ w, ‖(y w).1.1‖ := (le_prod_opNorm y).1
  have h₀ : Integrable P m := by
    simpa using V.integrable_mul_tripleKernel hB φ he hγ (a := 1) measurable_one
      fun _ y u ↦ abs_one.trans_le (one_le_mul_of_one_le_of_one_le (one_le y) (one_le u))
  have h₁ : Integrable (fun p ↦ a₁ p * P p) m :=
    V.integrable_mul_tripleKernel hB φ he hγ (by fun_prop) fun x y u ↦
      (h_lip x.1 y).trans (le_mul_of_one_le_right (by positivity) (one_le u))
  have h₂ : Integrable (fun p ↦ a₂ p * P p) m :=
    V.integrable_mul_tripleKernel hB φ he hγ (by fun_prop) fun x y u ↦
      (h_lip (x.1 * y) u).trans (le_mul_of_one_le_left (by positivity) (one_le y))
  have h₁₂ : Integrable (fun p ↦ a₁ p * P p + a₂ p * P p) m := h₁.add h₂
  have h₃ : Integrable (fun p ↦ a₃ p * P p) m :=
    ((h₀.const_mul ℓ).sub h₁₂).congr (.of_forall fun p ↦ sub_eq_of_eq_add' (h_sum p))
  -- As `e ⋆ e = e`, the integral of `P` is `I_γ`, and that of `(a₁ + a₂) P` is that of `a₁ P`.
  have h_orb : ∫ p, P p ∂m = V.orbitalIntegral e φ γ := by
    rw [V.integral_tripleMeasure h₀ (.id _)]
    simp only [P, tripleKernel, id, integral_const_mul, integral_mul_const, he.convolution_self,
      orbitalIntegral, orbitalIntegrand]
  have h_add (p : G E s × GInf E s × GInf E s) : a₁ p * P p + a₂ p * P p =
      (H (p.1.1 * (p.2.1 * p.2.2)) - H p.1.1 : ℝ) * P p := by
    simp [a₁, a₂, mul_assoc, ← add_mul]
  have h_zero : ∫ p, a₂ p * P p ∂m = 0 := by
    rw [← add_eq_left (a := ∫ p, a₁ p * P p ∂m), ← integral_add h₁ h₂]
    simp only [h_add] at h₁₂ ⊢
    exact V.integral_mul_tripleKernel_mul φ he (b := fun x y ↦ H (x.1 * y) - H x.1) h₁₂ h₁
  -- The rotation carries `a₁` to `a₂` and `a₂` to `a₃`, so the three integrals agree.
  have h_incr {t : U V.J} (ht : Commute γ t) (a b : GInf E s) :
      H ((V.ratEmbed t).1 * a) - H ((V.ratEmbed t).1 * b) = H a - H b := by
    obtain ⟨r, hr⟩ := h_cent t ht
    simp [hr]
  have h₂₁ : ∫ p, a₂ p * P p ∂m = ∫ p, a₁ p * P p ∂m :=
    V.integral_mul_tripleKernel_tripleRotate φ h_meas (by fun_prop) h₁ h₂ (fun p ↦ rfl)
      fun t ht x q ↦ by simp only [a₁, Prod.fst_mul, mul_assoc, h_incr ht]
  have h₃₂ : ∫ p, a₃ p * P p ∂m = ∫ p, a₂ p * P p ∂m :=
    V.integral_mul_tripleKernel_tripleRotate φ h_meas (by fun_prop) h₂ h₃
      (fun p ↦ by simp [a₂, a₃, tripleRotate, mul_assoc, h_shift])
      fun t ht x q ↦ by simp only [a₂, Prod.fst_mul, mul_assoc, h_incr ht]
  calc ℓ * V.orbitalIntegral e φ γ
      = ∫ p, a₁ p * P p + a₂ p * P p + a₃ p * P p ∂m := by
        simp only [← h_orb, ← integral_const_mul, h_sum]
    _ = 0 := by rw [integral_add h₁₂ h₃, integral_add h₁ h₂, h₃₂, ← h₂₁, h_zero, add_zero, add_zero]

/-- The Selberg principle: let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`. If the characteristic
polynomial of the rational point `γ` is irreducible and its `i`-th complex root (`numberedRoots`)
under the embedding `Φ w` at the infinite place `w` lies off the unit circle, then the orbital
integral of `e ⊗ φ` at `γ` is zero. -/
theorem orbitalIntegral_eq_zero [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {γ : U V.J}
    (hγ : Irreducible (γ : GL n E).val.charpoly) {w : InfinitePlace E} {i : n}
    (h_root : ‖numberedRoots (Φ w) (γ : GL n E).val.charpoly i‖ ≠ 1) :
    V.orbitalIntegral e φ γ = 0 := by
  -- Let `ℓ ≠ 0` be the logarithm of the modulus of the root, and `H y` the logarithm of the norm
  -- of the `i`-th row of `k y`, with `k` diagonalising `γ` at `w`. Then `H (γ y) = ℓ + H y`.
  let A : Matrix n n ℂ := ((V.ratEmbed γ).1 w).1.1
  let d : n ↪ ℂ := numberedRoots (Φ w) γ.1.1.charpoly
  obtain ⟨k, hk⟩ : ∃ k : (Matrix n n ℂ)ˣ, SemiconjBy k.1 A (diagonal d) := by
    refine IsConj.symm (isConj_diagonal_of_isRoot_charpoly fun j ↦ ?_)
    have hA : A = (V.x.map (evalInf w))⁻¹.1 * γ.1.1.map (Φ w) * (V.x.map (evalInf w)).1 :=
      V.coe_ratEmbed_fst γ w
    rw [hA, charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    exact isRoot_numberedRoots hγ.separable (Φ w) j
  let Q : Matrix n n ℂ := diagonal (Pi.single i 1) * k.1
  have hQ_ne : Q ≠ 0 := by simp [Q]
  let H (y : GInf E s) : ℝ := ‖Q * (y w).1.1‖.log
  have hQ_mul (y : GInf E s) : Q * (y w).1.1 ≠ 0 := (y w).1.isUnit.mul_left_eq_zero.ne.2 hQ_ne
  -- An element that multiplies `Q` by a scalar `m` shifts `H` by `log ‖m‖`.
  have h_ne {t : GInf E s} {m : ℂ} (ht : Q * (t w).1.1 = m • Q) : m ≠ 0 :=
    fun h ↦ hQ_mul t (by rw [ht, h, zero_smul])
  have hH {t : GInf E s} {m : ℂ} (ht : Q * (t w).1.1 = m • Q) (y : GInf E s) :
      H (t * y) = ‖m‖.log + H y := by
    have h_mul : Q * ((t * y) w).1.1 = m • (Q * (y w).1.1) := by
      simp [← smul_mul_assoc, ← ht, mul_assoc]
    simp only [H, h_mul, norm_smul]
    exact Real.log_mul (norm_ne_zero_iff.2 (h_ne ht)) (norm_ne_zero_iff.2 (hQ_mul y))
  have hQ {t : Matrix n n ℂ} (ht : Commute t A) : Q * t = (k * t * k⁻¹.1) i i • Q :=
    row_mul_eq_smul_of_commute hk ht i
  have hQA : Q * A = d i • Q := by simpa [hk.eq] using hQ (.refl A)
  have hℓ : (‖d i‖.log : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 (h_ne hQA)) h_root)
  have h_lip (a b : GInf E s) : |H (a * b) - H a| ≤ ∏ v, ‖(b v).1.1‖ :=
    (abs_log_norm_mul_sub_le hQ_ne w a b).trans ((le_prod_opNorm b).2 w)
  have h_cent (t : U V.J) (ht : Commute γ t) :
      ∃ r : ℝ, ∀ y, H ((V.ratEmbed t).1 * y) = r + H y := by
    have h_comm : Commute ((V.ratEmbed t).1 w).1.1 A :=
      congrArg (fun g : G E s ↦ (g.1 w).1.1) (ht.map V.ratEmbed).symm.eq
    exact ⟨_, hH (hQ h_comm)⟩
  have h_mul_zero : (‖d i‖.log : ℂ) * V.orbitalIntegral e φ γ = 0 :=
    V.mul_orbitalIntegral_eq_zero hB φ he hγ (by fun_prop) h_lip (hH hQA) h_cent
  exact (mul_eq_zero.1 h_mul_zero).resolve_left hℓ

/-- An irreducible polynomial `R` whose `i`-th complex root at the infinite place `w` lies off the
unit circle does not contribute to the geometric side for `e ⊗ φ` (the integral over `Γ \ G` of the
terms of the rational points with characteristic polynomial `R` is zero). Here `e` is a cusp kernel
of order `B ≥ 13 n ^ 3`. -/
theorem geometricSide_singleton_eq_zero_of_norm_ne_one [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {R : E[X]} (hR : Irreducible R)
    {w : InfinitePlace E} {i : n} (h_root : ‖numberedRoots (Φ w) R i‖ ≠ 1) :
    V.geometricSide hB he {R} φ = 0 := by
  have h_class (c : FrameClass E n) : V.classIntegral e φ R c = 0 := by
    by_contra hc
    obtain ⟨γ, rfl, rfl⟩ := V.exists_frameClass_eq_of_classIntegral_ne_zero hc
    rw [(V.orbitalIntegral_unfold hB φ he.decay he.continuous.measurable hR).2] at hc
    exact hc (V.orbitalIntegral_eq_zero hB φ he hR h_root)
  refine (V.hasSum_classIntegral hB φ he.decay he.continuous.measurable hR).unique ?_
  rw [_root_.funext h_class]
  exact hasSum_zero

/-! ### All roots on the unit circle -/

/-- A rational point `γ` is an elliptic similitude of `V.J` with multiplier `1` if its
characteristic polynomial is irreducible with all complex roots on the unit circle. -/
lemma isEllipticSimilitude_of_norm_eq_one {γ : U V.J} (hγ : Irreducible (γ : GL n E).val.charpoly)
    (h_norm : ∀ (w : InfinitePlace E) (i : n),
      ‖numberedRoots (Φ w) (γ : GL n E).val.charpoly i‖ = 1) :
    IsEllipticSimilitude 1 γ V.J := by
  refine ⟨hγ, one_ne_zero, by simp [← mem_U], fun w r hr ↦ ?_⟩
  rw [roots_eq_map_numberedRoots hγ.separable] at hr
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
  simp [mul_conj', h_norm]

/-- Splitting of an orbital integral into real and finite factors, for the product
`typeKernel l s` of the discrete series kernels of parameters `l w`. Let the rational point `γ` be
conjugate by `g` to `(t, y)`, and let `β` be a function on `G_f` such that `x ↦ β (g⁻¹ x)_f` is a
cutoff (a weight of sum one on each orbit) for the rational centraliser of `γ`. Then `I_γ` is the
product of the real orbital integrals at the `t w` and the finite orbital integral at `y`, which is
written with `β`. -/
theorem orbitalIntegral_eq_prod_mul (φ : TestFunction (Gf E n)) {l : InfinitePlace E → n → ℤ}
    (hl : Measurable (typeKernel l s)) {γ : U V.J} {g : G E s} {t : GInf E s} {y : Gf E n}
    (hγ : V.ratEmbed γ = g * (t, y) * g⁻¹) {β : Gf E n → ℝ≥0∞}
    (hβ : IsCutoff (Measure.count : Measure ((centralizer {γ}).map V.ratEmbed))
      fun x : G E s ↦ β (g⁻¹ * x).2) :
    V.orbitalIntegral (typeKernel l s) φ γ =
      (∏ w : InfinitePlace E, ∫ h : USign s, (toHCParam s (l w)).dsKernel (h⁻¹ * t w * h)) *
        ∫ v : Gf E n, (β v).toReal • (φ : Gf E n → ℂ) (v⁻¹ * y * v) := by
  -- Insert the cutoff, translate by `g`, and split `G` into its real and finite parts.
  rw [orbitalIntegral,
    hβ.integral_orbitMeasure (fun u ↦ V.fixesLeft_orbitalIntegrand (typeKernel l s) φ γ _ u.2)
      (V.measurable_orbitalIntegrand hl φ γ),
    ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [typeKernel, orbitalIntegrand, hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply,
    mul_smul_comm]

/-- Let `y` be an elliptic isometry (multiplier `1`) of a form with Gram matrix `1` in the finite
frame `x` and the sign `s i` on the eigenline of the root `z w (σ w i)`. Then there is a space of
signs `s` with finite frame `x` in which `y` is an isometry, with real component
`diag(z w ∘ σ w)` at each place `w`. -/
lemma exists_ratEmbed_eq_diagTorus {x : GL n (𝔸f E)} {y : GL n E} {σ : InfinitePlace E → Perm n}
    (hx : HasSignType (fun w : InfinitePlace E ↦ s ∘ (σ w).symm) 1 y {1} x)
    {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) y.val.charpoly i) :
    ∃ W : Space E n s, W.xFin = x ∧
      ∃ hy : y ∈ U W.J, ∀ w : InfinitePlace E,
        (W.ratEmbed ⟨y, hy⟩).1 w = diagTorus s (z w ∘ σ w) := by
  obtain ⟨β, h_ell, h_frame, h_pos⟩ := hx
  -- At each infinite place an eigenbasis of `y`, in the order `σ w`, has Gram matrix
  -- `signMatrix s`.
  have h_basis (w : InfinitePlace E) : ∃ k : GL n ℂ, k.1ᴴ * β.map (Φ w) * k = signMatrix s ∧
      k⁻¹.1 * y.1.map (Φ w) * k = diagonal fun i ↦ numberedRoots (Φ w) y.1.charpoly (σ w i) := by
    obtain ⟨k, d, -, h_pos_iff, h_signs⟩ := exists_eigenbasis_diag_form h_ell w (σ w)
    have h_sign (i : n) : 0 < d i * s i := by
      simpa only [eval_interpolate_univ_node, Function.comp_apply, symm_apply_apply]
        using (h_pos_iff _).1 (h_pos w) i
    exact h_signs s h_sign
  choose k h_gram h_eigen using h_basis
  let W : Space E n s :=
    { J := β
      x := mkAdelicGL (k, x)
      gram_point := gram_mkAdelicGL h_gram h_frame }
  have hy : y ∈ U β := by simpa [mem_U] using h_ell.conjTranspose_mul_mul
  refine ⟨W, rfl, hy, fun w ↦ ?_⟩
  have h_point : W.x.map (evalInf w) = k w := rfl
  have h_torus : (diagTorus s (z w ∘ σ w)).1.1 =
      diagonal fun i ↦ numberedRoots (Φ w) y.1.charpoly (σ w i) := by
    simp only [← hz]
    rfl
  ext : 2
  rw [h_torus, coe_ratEmbed_fst, h_point, h_eigen w]

/-- If the finite frames of two spaces conjugate the rational centraliser of `y` in the same way,
then the image in `G_f` of the centraliser of `y` in the first unitary group lies in that for the
second. -/
lemma map_embFin_centralizer_le {s' : n → ℤˣ} (W : Space E n s') {y : GL n E} (hy : y ∈ U V.J)
    (hy' : y ∈ U W.J) (h_conj : ∀ a : GL n E, Commute y a →
      V.xFin⁻¹ * toFinGL a * V.xFin = W.xFin⁻¹ * toFinGL a * W.xFin) :
    (centralizer {⟨y, hy⟩}).map V.embFin ≤ (centralizer {⟨y, hy'⟩}).map W.embFin := by
  rintro _ ⟨⟨a, ha⟩, h_cent, rfl⟩
  have h_comm : Commute y a := (Subtype.ext_iff.1 (mem_centralizer_singleton_iff.1 h_cent)).symm
  -- `a` is an isometry of `V` or `W` exactly if its conjugate by the frame is unitary.
  have ha' : a ∈ U W.J := by
    rwa [mem_U, ← W.mem_U_one_iff_gram_eq gram_xFin, ← h_conj a h_comm,
      V.mem_U_one_iff_gram_eq gram_xFin]
  refine ⟨⟨a, ha'⟩, mem_centralizer_singleton_iff.2 (Subtype.ext h_comm.symm), ?_⟩
  simp [Gf.val_ext_iff, coe_embFin, h_conj a h_comm]

/-- If the finite frames of two spaces conjugate the rational centraliser of `y` in the same way,
then the centralisers of `y` in the two unitary groups have the same image in `G_f`. -/
lemma map_embFin_centralizer_eq {s' : n → ℤˣ} (W : Space E n s') {y : GL n E} (hy : y ∈ U V.J)
    (hy' : y ∈ U W.J) (h_conj : ∀ a : GL n E, Commute y a →
      V.xFin⁻¹ * toFinGL a * V.xFin = W.xFin⁻¹ * toFinGL a * W.xFin) :
    (centralizer {⟨y, hy⟩}).map V.embFin = (centralizer {⟨y, hy'⟩}).map W.embFin :=
  (V.map_embFin_centralizer_le W hy hy' h_conj).antisymm
    (W.map_embFin_centralizer_le V hy' hy fun a ha ↦ (h_conj a ha).symm)

/-- The inverse of a group isomorphism `f` maps the centraliser of `f a` onto that of `a`. -/
lemma map_symm_centralizer_singleton {M N : Type*} [Group M] [Group N] (f : M ≃* N) (a : M) :
    (centralizer {f a}).map f.symm.toMonoidHom = centralizer {a} := by
  ext b
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulEquiv.symm_symm, ← map_mul, ← map_mul, f.apply_eq_iff_eq]

/-- Let `E` contain the 5040th roots of unity. Let `y` be an elliptic isometry of a positive form
with orthonormal finite frame `u` (`HasSignType 1 1 y {1} u`), and let `z w` list the roots of its
characteristic polynomial at the place `w`. There is a number `c`, the finite orbital integral of
`φ`, with the following property. Suppose `typeKernel l s`, the product over `w` of the discrete
series kernels `dsKernel` for the parameters `l w`, is a cusp kernel of order `B ≥ 13 n ^ 3`.
Suppose `y` is an elliptic isometry of a form with orthonormal finite frame `x` and signs `s` at the
roots in the order `σ`. Suppose also that `x` conjugates the rational centraliser of `y` as `u`
does. Then on a space `V` of signs `s`, `V.classIntegral` of the class of `(x, y)` is `c` times the
product over `w` of the integrals over `U(diag s)` of `dsKernel` at conjugates of
`diag(z w ∘ σ w)`. -/
theorem exists_classIntegral_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] {u : GL n (𝔸f E)} {y : GL n E}
    (hu : HasSignType 1 1 y {1} u) {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) y.val.charpoly i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ}
      {σ : InfinitePlace E → Perm n} {x : GL n (𝔸f E)}, IsCuspKernel B (typeKernel l s) →
      HasSignType (fun w : InfinitePlace E ↦ s ∘ (σ w).symm) 1 y {1} x →
      (∀ a : GL n E, Commute y a → u⁻¹ * toFinGL a * u = x⁻¹ * toFinGL a * x) →
      V.classIntegral (typeKernel l s) φ y.val.charpoly (frameClass (x, y)) =
        (∏ w : InfinitePlace E, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
  -- The constant is the finite orbital integral in the definite space `W₀` with frame `u`.
  obtain ⟨W₀, rfl, hy₀, -⟩ := exists_ratEmbed_eq_diagTorus (s := 1) (σ := 1) hu hz
  -- The centraliser is cut with `W₀.Γf`, which contains it, so that it is seen to be discrete.
  obtain ⟨β, hβ_meas, hβ⟩ : ∃ β : Gf E n → ℝ≥0∞, IsCutoff
      (Measure.count : Measure ↥(W₀.Γf ⊓ (centralizer {⟨y, hy₀⟩}).map W₀.embFin)) β :=
    (hasCutoff_count _).out
  refine ⟨∫ v, (β v).toReal • φ.1 (v⁻¹ * W₀.embFin ⟨y, hy₀⟩ * v),
    fun {s} V l σ x he hx same_conj ↦ ?_⟩
  -- `W` is a space of signs `s` with frame `x` in which `y` is diagonal at infinity.
  obtain ⟨W, rfl, hy, h_diag⟩ := exists_ratEmbed_eq_diagTorus hx hz
  -- Landherr: `b` is a rational isometry from `W.J` to `V.J`, and conjugation by `b` becomes
  -- conjugation by `g ∈ G` under the embeddings.
  obtain ⟨b, g, hb, -, emb_conj⟩ := V.exists_x_eq_and_ratEmbed_conj_eq W
  set conj : U W.J ≃* U V.J := U.conj b hb
  let γ : U V.J := conj ⟨y, hy⟩
  have class_eq : frameClass (V.xFin, γ.1) = frameClass (W.xFin, y) :=
    frameClass_eq_iff.2 ⟨b, (V.mem_U_one_iff_gram_eq gram_xFin).2 hb, rfl⟩
  -- By `same_conj`, `y` and its centraliser have the same finite images for `W₀` and for `W`.
  have embf_eq : W₀.embFin ⟨y, hy₀⟩ = W.embFin ⟨y, hy⟩ := by
    simp [Gf.val_ext_iff, coe_embFin, same_conj]
  have centralizer_eq : W₀.Γf ⊓ (centralizer {⟨y, hy₀⟩}).map W₀.embFin =
      (centralizer {γ}).map (W.embFin.comp conj.symm) := by
    rw [inf_eq_right.2 (map_le_range _ _), W₀.map_embFin_centralizer_eq W hy₀ hy same_conj,
      ← map_symm_centralizer_singleton conj, Subgroup.map_map]
    rfl
  -- So `β` of the finite part of `g⁻¹ x` is a cutoff for the centraliser of `γ` in `V`.
  have cutoff : IsCutoff (Measure.count : Measure ((centralizer {γ}).map V.ratEmbed))
      fun x : G E s ↦ β (g⁻¹ * x).2 := by
    refine ⟨by fun_prop, fun x ↦ ?_⟩
    have emb_eq (a : U V.J) : V.ratEmbed a = g * W.ratEmbed (conj.symm a) * g⁻¹ := by
      rw [← emb_conj, MulEquiv.apply_symm_apply]
    rw [← hβ (g⁻¹ * x).2, centralizer_eq, lintegral_count, lintegral_count]
    calc _ = ∑' a : centralizer {γ}, β (g⁻¹ * (V.ratEmbed a * x)).2 :=
          tsum_image (fun t : G E s ↦ β (g⁻¹ * (t * x)).2) V.ratEmbed_injective.injOn
      _ = ∑' a : centralizer {γ}, β (W.embFin (conj.symm a) * (g⁻¹ * x).2) := by
          simp [embFin, mul_assoc, emb_eq]
      _ = ∑' t : (centralizer {γ}).map (W.embFin.comp conj.symm), β (t • (g⁻¹ * x).2) :=
          (tsum_image (fun t : Gf E n ↦ β (t * (g⁻¹ * x).2))
            (W.fact_embFin_injective.1.comp conj.symm.injective).injOn).symm
  have h_poly : γ.1.1.charpoly = y.1.charpoly := by simp [γ, conj]
  have h_irr : Irreducible γ.1.1.charpoly := by
    obtain ⟨_, h_ell, -⟩ := hu
    simpa only [h_poly] using h_ell.irreducible_charpoly
  have h_embed : V.ratEmbed γ =
      g * (fun w ↦ diagTorus s (z w ∘ σ w), W₀.embFin ⟨y, hy₀⟩) * g⁻¹ := by
    rw [emb_conj, embf_eq, ← _root_.funext h_diag]
    rfl
  have h_unfold : V.classIntegral (typeKernel l s) φ (γ : Matrix n n E).charpoly
      (frameClass (V.xFin, (γ : GL n E))) = V.orbitalIntegral (typeKernel l s) φ γ :=
    (V.orbitalIntegral_unfold hB φ he.decay he.continuous.measurable h_irr).2
  rw [← class_eq, ← h_poly, h_unfold,
    V.orbitalIntegral_eq_prod_mul φ he.continuous.measurable h_embed cutoff]

/-- Matching the classes. Let `E` contain the 5040th roots of unity, and let `ε`, `ε'` be families
of signs, each with product `1`. There is a permutation `f` of the classes of pairs (finite frame,
rational matrix) that carries those with polynomial `R` and signs `ε` onto those with polynomial
`R` and signs `ε'`. If `(u, y)` has the signs `ε` (`y` is an elliptic isometry, with the signs `ε`
on its eigenlines, of a form with orthonormal frame `u`), then `f` sends its class to the class of
a pair `(x, y)` with signs `ε'` such that `u` and `x` conjugate the rational centraliser of `y` in
the same way. -/
theorem exists_perm_signedClasses [HasPrimitiveRoot5040 E] {ε ε' : InfinitePlace E → n → ℤˣ}
    (hε : ∏ w : InfinitePlace E, ∏ i : n, ε w i = 1)
    (hε' : ∏ w : InfinitePlace E, ∏ i : n, ε' w i = 1) (R : E[X]) :
    ∃ f : Perm (FrameClass E n), f '' signedClasses R ε = signedClasses R ε' ∧
      ∀ (u : GL n (𝔸f E)) (y : GL n E) (_hu : HasSignType ε 1 y {1} u),
        ∃ x : GL n (𝔸f E), HasSignType ε' 1 y {1} x ∧
          f (frameClass (u, y)) = frameClass (x, y) ∧
          ∀ a : GL n E, Commute y a → u⁻¹ * toFinGL a * u = x⁻¹ * toFinGL a * x := by
  -- The frame is moved by an adelic matrix `Z y` that commutes with the centraliser of `y` and
  -- changes the signs by `ε / ε'`.
  have h_prod : ∏ w, ∏ i, (ε'⁻¹ * ε) w i = 1 := by simp [prod_mul_distrib, hε, hε']
  obtain ⟨f, hf⟩ := exists_hasSignType_mul_iff (fun _ : Unit ↦ ε'⁻¹ * ε) (fun _ ↦ h_prod) (U 1)
  have h_move (y : GL n E) : ∃ Z : GL n (𝔸f E),
      (∀ u, HasSignType ε 1 y {1} u ↔ HasSignType ε' 1 y {1} (Z * u)) ∧
      (∀ a, Commute y a → Commute (toFinGL a) Z) ∧
      ∀ u, f (frameClass (u, y)) = frameClass (Z * u, y) := by
    obtain ⟨Z, h_sign, h_comm, h_map⟩ := hf y ()
    refine ⟨Z, fun u ↦ ?_, h_comm, fun u ↦ h_map ⟦u⟧⟩
    simpa using h_sign 1 ε' {1} u
  choose Z h_iff h_comm h_class using h_move
  refine ⟨f, Set.Subset.antisymm ?_ ?_, fun u y hu ↦
    ⟨Z y * u, (h_iff y u).1 hu, h_class y u, fun a ha ↦ ?_⟩⟩
  · rintro _ ⟨_, ⟨u, y, hy, hu, rfl⟩, rfl⟩
    exact ⟨Z y * u, y, hy, (h_iff y u).1 hu, (h_class y u).symm⟩
  · rintro _ ⟨x, y, hy, hx, rfl⟩
    exact ⟨_, ⟨(Z y)⁻¹ * x, y, hy, (h_iff y _).2 (by simpa using hx), rfl⟩, by simp [h_class]⟩
  · simp only [_root_.mul_inv_rev, mul_assoc, (h_comm y a ha).left_comm, inv_mul_cancel_left]

omit [DecidableEq n] in
/-- If the number of infinite places is even, a family of signs that is a rearrangement of the same
`s` at each place has product `1`. -/
lemma prod_prod_comp_symm_eq_one (hE : Even (Core.numInfPlaces E)) (s : n → ℤˣ)
    (σ : InfinitePlace E → Perm n) :
    ∏ w : InfinitePlace E, ∏ i : n, (s ∘ (σ w).symm) i = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, card (InfinitePlace E) = m + m := hE
  have h_place (w : InfinitePlace E) : ∏ i, (s ∘ (σ w).symm) i = ∏ i, s i := (σ w).symm.prod_comp s
  simp only [h_place, prod_const, card_univ, hm, pow_add, Int.units_mul_self]

/-- Let `E` contain the 5040th roots of unity and have an even number of infinite places, and let
`z` be the numbered roots of `R`, on the unit circle. There is a number `c` with the following
property. On every space, suppose the product `typeKernel l s` of the discrete series kernels is a
cusp kernel of order `B ≥ 13 n ^ 3`. Then the contributions of the classes with polynomial `R` and
signs `s` in the order `σ` of the roots add up to the product of the real orbital integrals times
`c`. These classes are `signedClasses`: classes of pairs `(x, y)` with `y` an elliptic isometry of
characteristic polynomial `R`, with those signs on its eigenlines, of a form for which `x` is an
orthonormal frame. -/
theorem exists_tsum_signedClasses_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    {R : E[X]} {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) R i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ},
      IsCuspKernel B (typeKernel l s) → ∀ σ : InfinitePlace E → Perm n,
      ∑' a : signedClasses R fun w : InfinitePlace E ↦ s ∘ (σ w).symm,
          V.classIntegral (typeKernel l s) φ R a =
        (∏ w : InfinitePlace E, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
  -- Match the classes with those of signs `1`, and add up their finite orbital integrals `C a`.
  have h_repr (a : signedClasses (n := n) R 1) : ∃ (u : GL n (𝔸f E)) (y : GL n E),
      y.1.charpoly = R ∧ HasSignType 1 1 y {1} u ∧ frameClass (u, y) = a := a.2
  choose u y h_poly h_sign h_rep using h_repr
  choose C hC using fun a ↦
    exists_classIntegral_eq hB φ (h_sign a) (z := z) (by simpa only [h_poly] using hz)
  refine ⟨∑' a, C a, fun {s} V l he σ ↦ ?_⟩
  obtain ⟨f, h_image, hf⟩ :=
    exists_perm_signedClasses (ε := 1) (by simp) (prod_prod_comp_symm_eq_one hE s σ) R
  rw [← h_image, tsum_image _ f.injective.injOn, ← tsum_mul_left]
  refine tsum_congr fun a ↦ ?_
  obtain ⟨x, hx, h_class, h_conj⟩ := hf (u a) (y a) (h_sign a)
  rw [← h_rep, h_class, ← hC a V he hx h_conj, h_poly]

/-- The class of an elliptic rational point `γ` has the signs `ε` exactly if the form of `V` has
these signs on the eigenlines of `γ`: at each infinite place `w` the matrix `V.J p(γ)` is positive
definite, where `p` takes the value `ε w i` at the `i`-th root. -/
lemma frameClass_mem_signedClasses_iff {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J)
    (ε : InfinitePlace E → n → ℤˣ) :
    frameClass (V.xFin, (γ : GL n E)) ∈ signedClasses (γ : GL n E).val.charpoly ε ↔
      ∀ w : InfinitePlace E,
        (V.J.map (Φ w) * aeval ((γ : GL n E).val.map (Φ w)) (Lagrange.interpolate univ
          (numberedRoots (Φ w) (γ : GL n E).val.charpoly) fun i : n ↦ (ε w i : ℂ))).PosDef := by
  refine ⟨?_, fun h_pos ↦ ⟨V.xFin, γ, rfl, ⟨V.J, hγ, by simp [gram_xFin], h_pos⟩, rfl⟩⟩
  rintro ⟨x, a, h_poly, ⟨β, -, h_frame, h_pos⟩, h_class⟩ w
  -- The rational matrix `g` that identifies the classes carries `V.J` to the form `β` of `a`.
  obtain ⟨g, hg, hgγ⟩ : ∃ g : GL n E, V.xFin⁻¹ * toFinGL g * x ∈ U 1 ∧ g * a * g⁻¹ = γ :=
    frameClass_eq_iff.1 h_class.symm
  obtain rfl : g.1ᴴ * V.J * g.1 = β := (V.mem_U_one_iff_gram_eq h_frame).1 hg
  -- Conjugation by `g` keeps positivity and turns the polynomial in `γ` into that in `a`.
  have h_conj : SemiconjBy (g.map (Φ w)).1 (a.1.map (Φ w)) (γ.1.1.map (Φ w)) := by
    simp [SemiconjBy, ← hgγ, ← Matrix.map_mul]
  have h_form : (g.1ᴴ * V.J * g.1).map (Φ w) =
      star (g.map (Φ w)).1 * V.J.map (Φ w) * (g.map (Φ w)).1 :=
    map_conjTranspose_mul_mul (Φ w) (by simp) g.1 V.J
  rw [← (g.map (Φ w)).isUnit.posDef_star_left_conjugate_iff, mul_assoc, mul_assoc,
    ← aeval_semiconj h_conj, ← h_poly, ← mul_assoc, ← mul_assoc, ← h_form]
  exact h_pos w

/-- At the infinite place `w` the frame `V.x` carries the form `V.J` to the diagonal matrix of the
signs `s`. -/
lemma gram_map_evalInf (w : InfinitePlace E) :
    (V.x.map (evalInf w)).valᴴ * V.J.map (Φ w) * (V.x.map (evalInf w)).val = signMatrix s := by
  have h_map : (V.x.1ᴴ * V.J.map toAdele * V.x.1).map (evalInf w) = signMatrix s := by
    simp [V.gram_point, stdForm, signMatrix]
  rwa [map_conjTranspose_mul_mul (evalInf w) fun _ ↦ rfl, Matrix.map_map] at h_map

/-- Let `γ` be an elliptic rational point of `V`. For a permutation `σ` take the polynomial with
value `s (σ⁻¹ i)` at the `i`-th eigenvalue of `γ` at `w`. The `σ` for which `V.J` times this
polynomial in `γ` is positive definite are as many as those that fix `s`. -/
lemma card_perm_posDef {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J) (w : InfinitePlace E) :
    Nat.card {σ : Perm n //
      (V.J.map (Φ w) * aeval ((γ : GL n E).val.map (Φ w)) (Lagrange.interpolate univ
        (numberedRoots (Φ w) (γ : GL n E).val.charpoly) fun i : n ↦ s (σ.symm i))).PosDef} =
      #{σ : Perm n | s ∘ σ = s} := by
  classical
  -- In an eigenbasis `k` of `γ` the form is `diagonal d`, and positivity is read off from `d`.
  obtain ⟨k, d, hd, h_pos, h_basis⟩ := exists_eigenbasis_diag_form hγ w 1
  have h_frame : (V.x.map (evalInf w))⁻¹.1ᴴ * signMatrix s * (V.x.map (evalInf w))⁻¹.1 =
      V.J.map (Φ w) := gram_inv_of_gram_eq (V.gram_map_evalInf w)
  -- The form is hermitian and invertible, so the `d i` are real and nonzero; `ε i` is their sign.
  obtain ⟨g, hg⟩ : ∃ g : GL n ℂ, g.1ᴴ * diagonal (fun i ↦ (s i : ℂ)) * g.1 = diagonal d :=
    ⟨_, gram_mul_of_gram_eq h_frame hd⟩
  have hd_unit : IsUnit (diagonal d) := by simp [← hg, Pi.isUnit_iff]
  have hd_herm : (diagonal d)ᴴ = diagonal d := by simp [← hg, Pi.star_def, mul_assoc]
  have hd_im (i : n) : (d i).im = 0 := conj_eq_iff_im.1 (by simpa using congrFun₂ hd_herm i i)
  have hd_re (i : n) : (d i).re ≠ 0 := fun h ↦
    ((isUnit_diagonal.1 hd_unit).apply i).ne_zero (Complex.ext h (hd_im i))
  let ε (i : n) : ℤˣ := if 0 < d i then 1 else -1
  have h_sign (i : n) (u : ℤˣ) : 0 < d i * u ↔ ε i = u := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp [ε]
    · simp [ε, Complex.lt_def, (hd_re i).le_iff_lt, hd_im i]
  -- By Sylvester's law `ε` is a rearrangement `s ∘ τ` of `s`.
  obtain ⟨k', hk', -⟩ := h_basis ε fun i ↦ (h_sign i _).2 rfl
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm n, ∀ i, s (τ i) = ε i :=
    sylvester_law_of_inertia (gram_mul_of_gram_eq h_frame hk')
  -- `σ` counts on the left iff `s ∘ σ⁻¹ = ε = s ∘ τ`, that is, iff `τ σ` fixes `s`.
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (subtypeEquiv (.mulLeft τ) fun σ ↦ ?_)
  rw [h_pos, σ.surjective.forall]
  simp only [Perm.coe_one, id, eval_interpolate_univ_node, h_sign, symm_apply_apply, ← hτ]
  exact funext_iff.symm

/-- The class of an elliptic rational point `γ` has the signs `s` in as many orders `σ` of the roots
as there are families, indexed by the infinite places, of permutations that fix `s`. -/
lemma card_mem_signedClasses {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J) :
    Nat.card {σ : InfinitePlace E → Perm n // frameClass (V.xFin, (γ : GL n E)) ∈
      signedClasses (γ : GL n E).val.charpoly fun w : InfinitePlace E ↦ s ∘ (σ w).symm} =
      ∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s} := by
  simp only [V.frameClass_mem_signedClasses_iff hγ, Function.comp_apply]
  -- The condition is one condition on `σ w` for each place `w`.
  rw [← _root_.funext (V.card_perm_posDef hγ), ← Nat.card_pi, ← Nat.card_congr subtypePiEquivPi]

/-- Let the doubled Harish-Chandra parameters `l w` have gap at least `500 n³ + 10 n⁵` and let `z w`
be regular points of the compact torus. The sum over all orders `σ` of the products of the real
orbital integrals of the discrete series kernels is the number of families of permutations that fix
`s` times the product of the conjugate characters of the compact group `U(n)` at the `z w`. The
signs in Harish-Chandra's formula cancel because the number of infinite places is even. -/
lemma sum_prod_integral_dsKernel [Nonempty n] (hE : Even (Core.numInfPlaces E))
    {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ w : InfinitePlace E, (toHCParam s (l w)).HasLargeGap (10 * card n ^ 5))
    (z : InfinitePlace E → n ↪ Circle) :
    ∑ σ : InfinitePlace E → Perm n, ∏ w : InfinitePlace E, ∫ h : USign s,
        (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h) =
      (∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s} : ℕ) *
        ∏ w : InfinitePlace E,
          star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) := by
  let I (w : InfinitePlace E) (σ : Perm n) : ℂ :=
    ∫ h : USign s, (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ) * h)
  let ε : ℂ := (-1) ^ #(Orbital.oppositePairs s)
  have h_place (w : InfinitePlace E) : ε * ∑ σ, I w σ = #{σ : Perm n | s ∘ σ = s} *
      star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) :=
    (Orbital.harish_chandra_degree_and_orbital (h_gap w)).2 (z w) (z w).injective
  have h_sign : ∏ _ : InfinitePlace E, ε = 1 := by
    rw [prod_const, ← pow_mul]
    exact (hE.mul_left _).neg_one_pow
  calc ∑ σ : InfinitePlace E → Perm n, ∏ w, I w (σ w)
      = ∏ w, ∑ σ, I w σ := (Fintype.prod_sum I).symm
    _ = ∏ w, ε * ∑ σ, I w σ := by rw [prod_mul_distrib, h_sign, one_mul]
    _ = _ := by simp only [h_place, prod_mul_distrib, Nat.cast_prod]

/-- Elliptic terms. Let `E` contain the 5040th roots of unity and have an even number of infinite
places, and let `R` be irreducible with all roots `z w i` on the unit circle. There is a number `c`,
independent of the space, its signs and `l`, such that for all parameters `l` with gap at least
`500 n³ + 10 n⁵` whose kernel is a cusp kernel of order `B ≥ 13 n ^ 3`, the integral over `Γ \ G` of
the terms with characteristic polynomial `R` is `c` times the product of the conjugate characters
of the compact group `U(n)`. -/
theorem exists_geometricSide_singleton_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    {R : E[X]} (hR : Irreducible R) {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) R i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ}
      (he : IsCuspKernel B (typeKernel l s)),
      ∀ (_h_gap : ∀ w : InfinitePlace E, (toHCParam s (l w)).HasLargeGap (10 * card n ^ 5)),
      V.geometricSide hB he {R} φ =
        c * ∏ w : InfinitePlace E,
          star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) := by
  classical
  obtain ⟨c, hc⟩ := exists_tsum_signedClasses_eq hB φ hE hz
  refine ⟨c, fun {s} V l he h_gap ↦ ?_⟩
  let I : FrameClass E n → ℂ := V.classIntegral (typeKernel l s) φ R
  let S (σ : InfinitePlace E → Perm n) : Set (FrameClass E n) :=
    signedClasses R fun w ↦ s ∘ (σ w).symm
  let N : ℕ := ∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s}
  have hN : (N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun _ _ ↦ card_ne_zero.2 ⟨1, by simp⟩)
  have h_sum : HasSum I (V.geometricSide hB he {R} φ) :=
    V.hasSum_classIntegral hB φ he.decay he.continuous.measurable hR
  -- A class that contributes lies in `S σ` for exactly `N` values of `σ`.
  have h_count (a : FrameClass E n) : ∑ σ, (S σ).indicator I a = N * I a := by
    by_cases ha : I a = 0
    · simp [Set.indicator, ha]
    obtain ⟨γ, rfl, rfl⟩ := V.exists_frameClass_eq_of_classIntegral_ne_zero ha
    have h_ell : IsEllipticSimilitude 1 γ V.J :=
      V.isEllipticSimilitude_of_norm_eq_one hR fun w i ↦ by rw [← hz, Circle.norm_coe]
    have h_card : #{σ | frameClass (V.xFin, γ.1) ∈ S σ} = N := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact V.card_mem_signedClasses h_ell
    simp only [Set.indicator, ← sum_filter, sum_const, nsmul_eq_mul, h_card]
  have h_parts : HasSum (fun a ↦ ∑ σ, (S σ).indicator I a) (∑ σ, ∑' a : S σ, I a) :=
    hasSum_sum fun σ _ ↦ hasSum_subtype_iff_indicator.1 (h_sum.summable.subtype (S σ)).hasSum
  refine mul_left_cancel₀ hN ?_
  calc N * V.geometricSide hB he {R} φ
      = ∑ σ, ∑' a : S σ, I a := (h_sum.mul_left _).unique (by simpa only [h_count] using h_parts)
    _ = (∑ σ : InfinitePlace E → Perm n, ∏ w, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
        rw [sum_mul]
        exact sum_congr rfl fun σ _ ↦ hc V he σ
    _ = N * (c * ∏ w, star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w)))) := by
        rw [sum_prod_integral_dsKernel hE h_gap z]
        ring

end Space

/-- Comparison of traces. Let the CM field `E` contain the 5040th roots of unity and have an even
number of infinite places, let `V`, `V'` be spaces of rank `n ≥ 2` over `E`, and let `l` be a family
of doubled Harish-Chandra parameters with gap at least `500 n³ + 10 n⁵` for the signs of both;
`typeKernel l s` is the product of their discrete series kernels. Let `K` be a level and `a` an
element of the group algebra of the finite adelic group. Suppose that the test function `a ⋆ 1_K`
is cuspidal at a split place `w`, and that the elements of its support are integral at `w'` with
`0` a simple root of the characteristic polynomial modulo `w'`. Then operators that act as `a` on
the forms of parameter `l` and level `K` on `V` and on `V'` have the same trace. -/
theorem trace_comparison [Nonempty n] [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    (hn : 2 ≤ card n) {s s' : n → ℤˣ} (V : Space E n s) (V' : Space E n s')
    {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ v : InfinitePlace E, (toHCParam s (l v)).HasLargeGap (10 * card n ^ 5))
    (h_gap' : ∀ v : InfinitePlace E, (toHCParam s' (l v)).HasLargeGap (10 * card n ^ 5))
    {K : Subgroup (Gf E n)} [hK : IsLevel K] {a : MonoidAlgebra ℂ (Gf E n)} {w w' : FinPlace E}
    (hw : w.IsSplit) (h_cusp : IsCuspidalAt hw (convIndicator hK.isOpen hK.isCompact a))
    (h_simple : ∀ g : Gf E n, (convIndicator hK.isOpen hK.isCompact a : Gf E n → ℂ) g ≠ 0 →
      HasSimpleZero (g.atPlace w'))
    {T : End ℂ (levelSpace (V.formRep (typeKernel l s)) K)}
    (hT : ∀ y : levelSpace (V.formRep (typeKernel l s)) K,
      (T y).val = (V.formRep (typeKernel l s)).asAlgebraHom a y.val)
    {T' : End ℂ (levelSpace (V'.formRep (typeKernel l s')) K)}
    (hT' : ∀ y : levelSpace (V'.formRep (typeKernel l s')) K,
      (T' y).val = (V'.formRep (typeKernel l s')).asAlgebraHom a y.val) :
    LinearMap.trace ℂ (levelSpace (V.formRep (typeKernel l s)) K) T =
      LinearMap.trace ℂ (levelSpace (V'.formRep (typeKernel l s')) K) T' := by
  -- Up to `vol K` each trace is the geometric side, a sum over characteristic polynomials `R`.
  let φ : TestFunction (Gf E n) := convIndicator hK.isOpen hK.isCompact a
  have hB : 13 * card n ^ 3 ≤ 10 * card n ^ 5 := by
    nlinarith [Nat.mul_le_mul_left (card n ^ 3) (Nat.pow_le_pow_left hn 2)]
  have he : IsCuspKernel (10 * card n ^ 5) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  have he' : IsCuspKernel (10 * card n ^ 5) (typeKernel l s') := isCuspKernel_typeKernel h_gap'
  -- The terms of each polynomial `R` agree: elliptic terms match, the others are zero.
  have h_term (R : E[X]) : V.geometricSide hB he {R} φ = V'.geometricSide hB he' {R} φ := by
    by_cases hR : Irreducible R
    · by_cases h_norm : ∀ (v : InfinitePlace E) (i : n), ‖numberedRoots (Φ v) R i‖ = 1
      · let z (v : InfinitePlace E) : n ↪ Circle :=
          (numberedRoots (Φ v) R).codRestrict _ fun i ↦ mem_sphere_zero_iff_norm.2 (h_norm v i)
        obtain ⟨c, hc⟩ := Space.exists_geometricSide_singleton_eq hB φ hE hR (z := z) fun _ _ ↦ rfl
        rw [hc V he h_gap, hc V' he' h_gap']
      · obtain ⟨v, i, h_root⟩ : ∃ v i, ‖numberedRoots (Φ v) R i‖ ≠ 1 := by simpa using h_norm
        rw [V.geometricSide_singleton_eq_zero_of_norm_ne_one hB φ he hR h_root,
          V'.geometricSide_singleton_eq_zero_of_norm_ne_one hB φ he' hR h_root]
    · rw [V.geometricSide_singleton_eq_zero hB he h_cusp h_simple hR,
        V'.geometricSide_singleton_eq_zero hB he' h_cusp h_simple hR]
  refine mul_left_cancel₀ (ofReal_ne_zero.2 (measureReal_pos_of_isLevel K).ne') ?_
  calc volume.real (K : Set (Gf E n)) * LinearMap.trace ℂ _ T
      = V.geometricSide hB he .univ φ := V.volume_mul_trace_eq hB he hT
    _ = ∑' R : E[X], V.geometricSide hB he {R} φ := (V.hasSum_geometricSide hB he φ).tsum_eq.symm
    _ = ∑' R : E[X], V'.geometricSide hB he' {R} φ := tsum_congr h_term
    _ = V'.geometricSide hB he' .univ φ := (V'.hasSum_geometricSide hB he' φ).tsum_eq
    _ = volume.real (K : Set (Gf E n)) * LinearMap.trace ℂ _ T' :=
        (V'.volume_mul_trace_eq hB he' hT').symm

end New

end
