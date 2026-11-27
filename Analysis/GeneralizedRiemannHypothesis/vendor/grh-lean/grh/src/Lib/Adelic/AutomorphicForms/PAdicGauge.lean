import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.General.LinearAlgebra.MatrixNormBounds
import Lib.PadicComparison.Descent.TestCategory

/-!
# The p-adic gauge of algebraic forms, class sums, and integral forms of a level

Fix a prime `p` and a map `ιₚ : ℂ →+* ℂ_[p]`, written ι in prose and given by the instance
`[ι : PadicPlace p]`. The gauge `New.weylGauge κ e g ξ` is the largest `p`-adic absolute value of a
coordinate of `g⁻¹ ι(ξ)`, for a finite adelic unitary point `g` acting in weight `(κ, e)`. It
measures the `p`-integrality of the values of algebraic forms (`New.AlgForm`). The file proves
invariance properties of the gauge, bounds the forms `New.deltaForm` on `New.stdSpace E n` that are
supported on one double coset, bounds class sums over `Γ \ G / K`, and studies the sizes of
algebraic forms whose level is cut out at finitely many split places.

## Main definitions and results

* `New.exists_mul_mem_integralAbove`: a rational point moves `g` to a point integral above `p`.
* `New.LevelPlaces.LevelForm`: forms of weight (κ, e) on which the level `New.levelOf` of H acts
  through χ, a finite-dimensional inner product space under the class sum of the Gram pairing.
* `New.gramForm_mem_embValRing`: the Gram pairing of two vectors of gauge at most one, for
  `ι ∘ conj` and for `ι`, is integral; `New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one`: so is
  the inner product of two such forms, after multiplication by a common multiple of the orders of
  the stabilisers.
* `New.LevelPlaces.LevelForm.valueCoord`, `New.LevelPlaces.LevelForm.valueMetric`: coordinates of a
  form in which the inner product has a rational matrix, if the classes have no nontrivial
  automorphisms.
* `New.Rows.weylGauge_classSum_le_one`: `p`-integrality (gauge `New.weylGauge` at most one) passes
  to the class sum after multiplication by a common multiple of the orders of the stabilisers.

Notions from other files:
* `New.weylGauge`: at the infinite place τ, g⁻¹ acts through its component at the prime induced by
  the embedding x ↦ ι(Φ_τ(x̄)) of E into ℂ_p.
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.
* `New.integralAbove`: the subgroup of finite adelic unitary points whose components at all primes
  above p are integral invertible matrices.
* `New.classSum`: the class sum of f, that is, the sum over the double cosets c in Γ\G/K of
  f(g_c)/#(Γ ∩ g_c K g_c⁻¹), with g_c a chosen representative; `New.classAut` is Γ ∩ gKg⁻¹.
* `New.stdLevel`: K₀ = G_f ∩ GL_n(Ô), the stabiliser of the standard lattice in the finite adelic
  unitary group G_f = `New.Gf`; `New.maxCompactAt n w` is its part supported at w and w̄.

## Relation to the literature

Known; see `Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms` and `Lib.Adelic.Hecke.ClassSums` for
sources.
-/

noncomputable section

/-!
## Invariance of the gauge, integral forms, weak approximation above p

* `New.GaugeLe`, `New.integralFormsAt`: bounds for forms, and the module of integral forms over the
  valuation ring `New.embValRing` of `ι`.
-/

namespace New

open NormedField Space IsUltrametricDist Matrix Function
open NumberField (InfinitePlace)

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ} {p : ℕ} [Fact p.Prime]
  (g d : Gf E n) {k : Gf E n}

/-! ### Weak approximation above `p` and properties of the gauge -/

/-- The extension to the finite adeles of an embedding `σ : E →+* ℂ_[p]` maps a unitary point that
is integral above `p` to an integral matrix with integral inverse. -/
lemma adeleExtension_mem_intGL (σ : E →+* ℂ_[p]) {k : Gf E n} (hk : k ∈ integralAbove n p) :
    GeneralLinearGroup.map (adeleExtension σ) k.val ∈ intGL n valuation.integer := by
  -- The place induced by `σ` lies above `p`, so the component of `k` there is an integral `k'`.
  obtain ⟨k', hk'⟩ : k.atPlace (placeOfEmb σ) ∈ intGL n (LocInt (placeOfEmb σ)).toSubring :=
    mem_localLevel.1 hk _ (natCast_mem_placeOfEmb σ)
  -- The extension of `σ` to the completion preserves the order of values, hence integrality.
  have h_int (x : LocField (placeOfEmb σ)) (hx : x ∈ (LocInt (placeOfEmb σ)).toSubring) :
      placeOfEmbExtension σ x ∈ valuation.integer :=
    (valuation_comap_placeOfEmbExtension_isEquiv σ).le_one_iff_le_one.mpr hx
  -- The extension to the adeles factors through the component at the induced place.
  change GeneralLinearGroup.map (placeOfEmbExtension σ) (k.atPlace (placeOfEmb σ)) ∈ _
  rw [← hk']
  exact ⟨GeneralLinearGroup.map (RingHom.restrict _ _ _ h_int) k', rfl⟩

variable (p) in
/-- Weak approximation above `p`: for finite adelic points `g`, `d` there is a rational point `γ` of
the definite space `V` (by default the standard one), embedded by `V.embFin`, such that `γ g` and
`d (γ g) d⁻¹` are integral at all primes above `p`. -/
lemma exists_mul_mem_integralAbove (V : Space E n 1 := stdSpace E n) :
    ∃ γ : U V.J,
      V.embFin γ * g ∈ integralAbove n p ∧
      d * (V.embFin γ * g) * d⁻¹ ∈ integralAbove n p := by
  -- The `x` with `x g` and `d x g d⁻¹` integral at all places form a nonempty open set. By weak
  -- approximation it contains some `γ h` with `γ` rational and `h` trivial above `p`.
  have h_open : IsOpen {x : Gf E n | x ∈ stdLevel E n ∧ d * x * d⁻¹ ∈ stdLevel E n} :=
    isOpen_stdLevel.inter (isOpen_stdLevel.preimage_of_continuous (f := (d * · * d⁻¹)))
  obtain ⟨⟨⟨_, γ, rfl⟩, h, hh⟩, h_int, h_conj⟩ :=
    (V.weak_approximation (finite_natCast_mem p)).exists_mem_open
      (h_open.preimage (continuous_snd.mul_const g)) ⟨(1, g⁻¹), by simp⟩
  -- The finite component of the product of `γ` and `(1, h)` is `V.embFin γ * h`.
  replace h_int : V.embFin γ * h * g ∈ stdLevel E n := by simpa [embFin] using h_int
  replace h_conj : d * (V.embFin γ * h * g) * d⁻¹ ∈ stdLevel E n := by simpa [embFin] using h_conj
  have h_triv : ∀ w : FinPlace E, ↑p ∈ w.1 → h.atPlace w = 1 := by simpa [Gf.trivialOn] using hh
  refine ⟨γ, mem_localLevel.2 fun w hw ↦ ?_, mem_localLevel.2 fun w hw ↦ ?_⟩
  · simpa [h_triv w hw] using mem_stdLevel_iff.1 h_int w
  · simpa [h_triv w hw] using mem_stdLevel_iff.1 h_conj w

variable [ι : PadicPlace p] {ξ : WeylIndex n κ → ℂ}

/-- The gauge of `γ ξ` at `γ g` is the gauge of `ξ` at `g`, for a rational point `γ`. -/
lemma weylGauge_embFin (γ : U (stdSpace E n).J) :
    weylGauge κ e ((stdSpace E n).embFin γ * g) ((stdSpace E n).weightRep κ e γ ξ) =
      weylGauge κ e g ξ := by
  -- At each infinite place `adeleExtension` restricts on `E` to the embedding that it extends, so
  -- the factor `γ⁻¹` of `(γ g)⁻¹` cancels the action of `γ` on `ξ`.
  have h_rat (τ : InfinitePlace E) :
      GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) ((stdSpace E n).embFin γ).val =
        GeneralLinearGroup.map (weightEmbedding ιₚ τ) γ.val :=
    GeneralLinearGroup.ext fun _ _ ↦ by simp [stdSpace_embFin, adeleExtension_algebraMap]
  have h_cancel (τ : InfinitePlace E) :
      GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ))
          ((stdSpace E n).embFin γ * g)⁻¹.val *
          GeneralLinearGroup.map (weightEmbedding ιₚ τ) γ.val =
        GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) g⁻¹.val := by
    rw [← h_rat, ← map_mul]
    simp [mul_assoc]
  simp only [weylGauge, map_weightRep, mulVec_mulVec, ← map_mul, Pi.mul_def, h_cancel]

/-- The gauge of a vector is unchanged when the point is multiplied on the right by an element
that is integral at the primes above `p`. -/
lemma weylGauge_mul_of_mem_integralAbove (hk : k ∈ integralAbove n p) :
    weylGauge κ e (g * k) ξ = weylGauge κ e g ξ := by
  -- An element integral above `p` acts by a matrix with integral entries, so it does not increase
  -- the sup norm; this is applied to `k` and to `k⁻¹`.
  have h_le {a : Gf E n} (ha : a ∈ integralAbove n p) (b : Gf E n) :
      weylGauge κ e (b * a⁻¹) ξ ≤ weylGauge κ e b ξ := by
    have h_entry (i j : WeylIndex n κ) :
        ‖weylRep κ e (fun τ : InfinitePlace E ↦
          GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) a.val) i j‖ ≤ 1 :=
      weylRep_entry_mem _ (fun _ ↦ adeleExtension_mem_intGL _ ha) i j
    simpa [weylGauge, ← Pi.mul_def] using norm_mulVec_le_of_nonneg zero_le_one h_entry (_ *ᵥ _)
  exact le_antisymm (by simpa using h_le (inv_mem hk) g) (by simpa using h_le hk (g * k))

/-- The gauge is homogeneous for the absolute value of scalars under `ι`. -/
lemma weylGauge_smul (c : ℂ) : weylGauge κ e g (c • ξ) = ‖ιₚ c‖ * weylGauge κ e g ξ := by
  have h_comp : ιₚ ∘ (c • ξ) = ιₚ c • (ιₚ ∘ ξ) := funext fun i ↦ map_mul ιₚ c (ξ i)
  simp [weylGauge, h_comp, mulVec_smul, norm_smul]

/-- At a point `k` that is integral above `p`, a vector has gauge at most one if and only if all
its coordinates have absolute value at most one under `ι`. -/
lemma weylGauge_le_one_iff (ξ : WeylIndex n κ → ℂ) (hk : k ∈ integralAbove n p) :
    weylGauge κ e k ξ ≤ 1 ↔ ∀ i : WeylIndex n κ, ‖ιₚ (ξ i)‖ ≤ 1 := by
  -- The gauge at `k` is the gauge at `1`, the sup norm of the coordinates.
  rw [← one_mul k, weylGauge_mul_of_mem_integralAbove 1 hk]
  simp [weylGauge, weylRep, pi_norm_le_iff_of_nonneg]

/-- The gauge is ultrametric: if every `f a` has gauge at most `C ≥ 0`, so does their sum. -/
lemma weylGauge_sum_le {α : Type*} {s : Finset α} {C : ℝ} {f : α → WeylIndex n κ → ℂ}
    (hC : 0 ≤ C) (hf : ∀ a ∈ s, weylGauge κ e g (f a) ≤ C) :
    weylGauge κ e g (∑ a ∈ s, f a) ≤ C := by
  have h_comp : ιₚ ∘ (∑ a ∈ s, f a) = ∑ a ∈ s, ιₚ ∘ f a := funext fun _ ↦ by simp
  simpa [weylGauge, h_comp, mulVec_sum] using norm_sum_le_of_forall_le_of_nonneg hC hf

/-! ### Integral forms -/

/-- The algebraic form `φ` (with `φ.val (γ g)` equal to `γ` acting on `φ.val g` for rational `γ`) is
bounded by `c` at `d`: for every `g`, the gauge of `φ g` at `g * d` is at most `c`. -/
def GaugeLe (c : ℝ) (φ : AlgForm (E := E) n κ e) : Prop :=
  ∀ g : Gf E n, weylGauge κ e (g * d) (φ.val g) ≤ c

/-- The valuation ring O_ι ⊂ ℂ of complex numbers whose image under ι : ℂ → ℂ_p has absolute
value at most 1. -/
noncomputable abbrev embValRing : ValuationSubring ℂ := (valuation.comap ιₚ).valuationSubring

/-- The O_ι-module of forms φ in S that are integral at d: the value φ(g) has gauge at most 1 at
gd for every g. -/
noncomputable def integralFormsAt (S : Submodule ℂ (AlgForm n κ e)) (d : Gf E n) :
    Submodule embValRing (AlgForm (E := E) n κ e) :=
  S.restrictScalars embValRing ⊓
    { carrier := Set.ofPred (GaugeLe d 1)
      add_mem' {φ ψ} hφ hψ g := by
        simpa [weylGauge, mulVec_add] using (norm_add_le_max _ _).trans (max_le (hφ g) (hψ g))
      zero_mem' := by simp [GaugeLe, weylGauge]
      smul_mem' a φ hφ g := (weylGauge_smul (g * d) a).trans_le
        ((mul_le_of_le_one_left (norm_nonneg _) a.2).trans (hφ g)) }

/-- The stabiliser of the standard lattice is integral at every set `S` of finite places. -/
lemma stdLevel_le_localLevel {S : Set (FinPlace E)} : stdLevel E n ≤ localLevel n S := fun _ hk ↦
  mem_localLevel.2 fun w _ ↦ mem_stdLevel_iff.1 hk w

/-- If the values of an algebraic form `φ` at the points integral above `p` have `ι`-integral
coordinates, then `φ g` has gauge at most `1` at `g` for every `g`. -/
lemma weylGauge_le_one_of_integralAbove (φ : AlgForm (E := E) n κ e)
    (h_coord : ∀ g ∈ integralAbove n p, ∀ i : WeylIndex n κ, ‖ιₚ (φ.val g i)‖ ≤ 1) (g : Gf E n) :
    weylGauge κ e g (φ.val g) ≤ 1 := by
  -- Move `g` by a rational `γ` to an element integral above `p`; the gauge does not change.
  obtain ⟨γ, hγ, -⟩ := exists_mul_mem_integralAbove p g 1
  have h_equivariant : φ.val ((stdSpace E n).embFin γ * g) =
      (stdSpace E n).weightRep κ e γ (φ.val g) := φ.property.2 γ g
  rw [← weylGauge_embFin g γ, ← h_equivariant]
  exact (weylGauge_le_one_iff _ hγ).2 (h_coord _ hγ)

end New

/-!
## Classes at a level and the gauge of delta forms

* `New.StdClasses`: the set of classes `Γ \ G_f / K` at a level `K`, where `G_f = New.Gf E n` is the
  finite adelic group and `Γ` is the image of its rational points.
* `New.Rows.weylGauge_deltaForm_le`: the values of the delta form made from `v` at `x` have gauge at
  most the gauge of `v` at `x`.
* `New.Rows.weylNormSq_deltaForm_le`: after any automorphism `σ` of `ℂ`, the values of the delta
  form have squared norm at most `#Aut(x)²` times that of `σ ∘ v`.
-/

section ClassReps

open NumberField DoubleCoset

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ} (K : Subgroup (Gf E n)) {χ : K →* ℂ}

/-- The set of classes of the standard space I_n for a subgroup K: double cosets of the finite
adelic unitary group by its rational points on the left and K on the right. -/
abbrev StdClasses : Type := DoubleCosets (stdSpace E n).Γf K

variable {K}

/-- The classes at level `K` have a system of representatives `r` whose members are all integral
at the primes above `p`. -/
lemma exists_reps_integralAbove (p : ℕ) [Fact p.Prime] :
    ∃ r : StdClasses K → Gf E n,
      (∀ c : StdClasses K, DoubleCoset.mk (stdSpace E n).Γf K (r c) = c) ∧
      ∀ c : StdClasses K, r c ∈ integralAbove n p := by
  -- Move the representative `c.out` by a rational element to make it integral above `p`.
  have h_exists (c : StdClasses K) :
      ∃ γ : U (stdSpace E n).J, (stdSpace E n).embFin γ * c.out ∈ integralAbove n p :=
    (exists_mul_mem_integralAbove p c.out 1).imp fun _ ↦ And.left
  choose γ hγ using h_exists
  refine ⟨fun c ↦ (stdSpace E n).embFin (γ c) * c.out, fun c ↦ ?_, hγ⟩
  -- `γ c * c.out` lies in the double coset of `c.out`.
  exact (c.eq_mk_iff_out.2 (rel_iff.2 ⟨_, ⟨γ c, rfl⟩, 1, K.one_mem, by simp⟩)).symm

variable [HasFiniteType stdRatPoints K] [Fact (χ =ᶠ[nhds 1] 1)]

noncomputable instance : Fintype (StdClasses K) := @.ofFinite _ HasFiniteType.finite_classes

/-- For a level K (an open subgroup of the stabiliser of the standard lattice) and χ with values of
finite order, the delta form attached to χ, x, v (the form supported on the double coset of x that
is made from the vector v) has, at every point g, gauge at ι at most the gauge of v at x. -/
lemma Rows.weylGauge_deltaForm_le [hK : IsLevel K] (hχ : ∀ k : K, IsOfFinOrder (χ k)) {p : ℕ}
    [Fact p.Prime] [PadicPlace p] {x : Gf E n} {v : WeylIndex n κ → ℂ} {g : Gf E n} :
    weylGauge κ e g ((deltaForm stdEmbFin ((stdSpace E n).weightRep κ e) χ x v).val.val g) ≤
      weylGauge κ e x v := by
  -- The value at `g` is a finite sum; by the ultrametric bound `weylGauge_sum_le` it is enough to
  -- bound each term `χ k • γ⁻¹ v`, where `k = x⁻¹ γ g` lies in `K` (the other terms vanish).
  have h_norm (k : K) : ‖ιₚ (χ k)‖ = 1 := (ιₚ.isOfFinOrder (hχ k)).norm_eq_one
  rw [deltaForm_apply]
  refine weylGauge_sum_le _ (norm_nonneg _) fun γ _ ↦ ?_
  split_ifs with hk
  · -- `g = γ⁻¹ x k` with `k` integral above `p`.
    have hk_int : x⁻¹ * stdEmbFin γ * g ∈ integralAbove n p := stdLevel_le_localLevel (hK.le hk)
    have h_gauge :
        weylGauge κ e g ((stdSpace E n).weightRep κ e γ⁻¹ v) = weylGauge κ e x v :=
      calc
        _ = weylGauge κ e ((stdSpace E n).embFin γ⁻¹ * x) ((stdSpace E n).weightRep κ e γ⁻¹ v) := by
          rw [← weylGauge_mul_of_mem_integralAbove ((stdSpace E n).embFin γ⁻¹ * x) hk_int]
          simp [mul_assoc]
        _ = weylGauge κ e x v := weylGauge_embFin x γ⁻¹
    simp [weylGauge_smul, h_norm, h_gauge]
  · simp [weylGauge]

/-- Let `χ` be a character of the subgroup `K` with values of finite order, trivial near `1`, where
`K` has finite type for the rational points (so there are finitely many double cosets of the
rational points and `K`), and `σ` a field automorphism of `ℂ`. The value at any `g` of the delta
form at `x` made from `v`, after applying `σ` to its coordinates, has squared norm
(`New.weylNormSq`) at most `#Aut(x)²` times that of `σ ∘ v`, where `Aut(x)` is the stabiliser
`New.classAut` of the coset `x K` among the rational points. -/
lemma Rows.weylNormSq_deltaForm_le (hχ : ∀ k : K, IsOfFinOrder (χ k)) (σ : ℂ ≃+* ℂ) (x : Gf E n)
    (v : WeylIndex n κ → ℂ) (g : Gf E n) :
    weylNormSq (σ ∘ (deltaForm stdEmbFin ((stdSpace E n).weightRep κ e) χ x v).val.val g) ≤
      Nat.card (classAut stdEmbFin.range K x) ^ 2 * weylNormSq (σ ∘ v) := by
  classical
  -- The value at `g` is a sum of at most `Nat.card (classAut ..)` terms. After applying `σ` each
  -- term has Gram norm at most that of `σ ∘ v`; use the triangle inequality.
  have h_inv (γ : U (stdSpace E n).J) :
      weylNormSq (σ ∘ (stdSpace E n).weightRep κ e γ v) = weylNormSq (σ ∘ v) := by
    simpa [weylNormSq, gramForm_apply] using
      congrArg Complex.re (gramForm_map_weightRep (e := e) (σ : ℂ →+* ℂ) γ v v)
  have h_norm (k : K) : ‖σ (χ k)‖ = 1 := (σ.toMonoidHom.isOfFinOrder (hχ k)).norm_eq_one
  have h_term (γ : U (stdSpace E n).J) :
      √(weylNormSq (σ ∘ if h : x⁻¹ * stdEmbFin γ * g ∈ K then
          χ ⟨x⁻¹ * stdEmbFin γ * g, h⟩ • (stdSpace E n).weightRep κ e γ⁻¹ v else 0)) ≤
        √(weylNormSq (σ ∘ v)) := by
    split
    · simp [h_inv, h_norm]
    · simp [weylNormSq]
  -- It is enough to compare the square roots; the sum has at most `#Aut(x)` terms.
  have h_card : (transporter K stdEmbFin x g).card ≤ Nat.card (classAut stdEmbFin.range K x) := by
    grind [card_transporter]
  rw [← Real.sqrt_le_sqrt_iff (by bound), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _), deltaForm_apply]
  calc
    _ ≤ ∑ γ ∈ transporter K stdEmbFin x g, √(weylNormSq (σ ∘ v)) :=
      (sqrt_weylNormSq_sum_le σ _ _).trans (Finset.sum_le_sum fun γ _ ↦ h_term γ)
    _ = (transporter K stdEmbFin x g).card * √(weylNormSq (σ ∘ v)) := by simp
    _ ≤ Nat.card (classAut stdEmbFin.range K x) * √(weylNormSq (σ ∘ v)) := by gcongr

end New

end ClassReps

/-!
## Algebraic forms of a level: class sum metrics and integral forms

Algebraic forms on the standard definite space `New.stdSpace` whose level is cut out at finitely
many split places, and their sizes under the automorphisms of ℂ and the embeddings ℂ → ℂ_l.

* `New.LevelPlaces`: two finite families of split places; `New.fockLetters`, `New.letterPoly`:
  substitution of sums of variables into the polynomial of a vector of weight κ.
* `New.LevelPlaces.LevelForm.innerAt`, `New.LevelPlaces.LevelForm.norm_map_inner_le`: the pairing
  after an automorphism σ of ℂ, and Cauchy–Schwarz for σ of the inner product.
* `New.LevelPlaces.LevelForm.integralForms`, `New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one`:
  forms integral at j : ℂ → ℂ_l, and integrality of their inner products.

A form takes values in coordinate vectors indexed by `New.WeylIndex`, paired by the integer matrix
`New.weylGram`.
-/

namespace New

open Matrix NumberField MvPolynomial ComplexConjugate ComplexOrder Subgroup Real «GL» Finset

section
section

variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n]
  [DecidableEq n]

/-! ### Places and letters -/

variable (E) in
/-- Two finite families of finite places of E, called the chosen places and the places of the
twist, all distinct, none of them conjugate to itself or to another. -/
structure LevelPlaces where
  /-- The index set of the chosen places. -/
  ChosenIndex : Type
  /-- The index set of the places of the twist. -/
  TwistIndex : Type
  /-- There are finitely many chosen places. -/
  [fintypeChosen : Fintype ChosenIndex]
  /-- There are finitely many places of the twist. -/
  [fintypeTwist : Fintype TwistIndex]
  /-- The chosen places. -/
  chosenPlace : ChosenIndex → FinPlace E
  /-- The places of the twist. -/
  twistPlace : TwistIndex → FinPlace E
  /-- No place of either family equals another place or the conjugate of one. -/
  apart : IsConjApart (chosenPlace ⊕ᵥ twistPlace)

/-- If none of the places `u i` is `w` or `w̄`, then every element of K₀ = `New.stdLevel` supported
at `w` and `w̄` lies in `levelOf u H`, the subgroup of elements of K₀ whose reductions at the `u i`
form an element of `H`. -/
lemma maxCompactAt_le_levelOf {ι : Type*} {u : ι → FinPlace E} {w : FinPlace E}
    {H : Subgroup ((i : ι) → GL n (ResField (u i)))} (hw : w ∉ (Set.range u).conjClosure) :
    maxCompactAt n w ≤ levelOf u H :=
  le_trans (b := stdLevel E n ⊓ Gf.trivialOn n (.range u)) (fun k hk ↦ by
    -- no `u i` is `w` or its conjugate, so `k` is trivial at every `u i`
    have h_ne (i : ι) : u i ≠ w ∧ star (u i) ≠ w :=
      ⟨fun h_eq ↦ hw (.inl ⟨i, h_eq⟩), fun h_eq ↦ hw (.inr ⟨i, by simp [← h_eq]⟩)⟩
    simp_all [Subgroup.mem_inf]) inf_trivialOn_le_levelOf

/-- The algebra map sending the variable (τ, i, h) to the sum of the variables (τ, i, a) over
the indices a with sign s(a) = c and ord(a) = h. -/
def fockLetters {Φ : Type} (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ) :
    MatrixPoly (Σ _ : Φ, n) ℂ →ₐ[ℂ] MvPolynomial (Φ × n × r) ℂ :=
  aeval fun x : (Σ _ : Φ, n) × ℕ ↦ ∑ a : r with s a = c ∧ ord a = x.2, X (x.1.1, x.1.2, a)

/-- The linear map sending ξ of weight κ to its polynomial `New.toPoly` ξ, with each variable
(τ, i, h) replaced by ∑ X(τ, i, a) over s(a) = c, ord(a) = h. -/
def letterPoly {Φ : Type} [Fintype Φ] [DecidableEq Φ] (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ)
    (κ : Φ → ℕ → ℕ) : (WeylIndexFamily (fun _ : Φ ↦ n) κ → ℂ) →ₗ[ℂ] MvPolynomial (Φ × n × r) ℂ :=
  (fockLetters (r := r) (n := n) (Φ := Φ) s ord c).toLinearMap ∘ₗ toPoly (fun _ ↦ n) κ

end

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-! ### Forms of a level and the class sum metric -/

/-- The class sum on the standard definite space: for a subgroup K and a function f on the finite
points, the sum of f(g_c) / #Aut(g_c) over the double cosets c of the rational points and K. -/
abbrev stdClassSum {X : Type*} [AddCommMonoid X] [Module ℚ X] :
    Subgroup (Gf E n) → (Gf E n → X) → X :=
  classSum (stdSpace E n).Γf

/-- The Cauchy–Schwarz inequality for class sums of any level `K`. Let `σ` be an automorphism of
`ℂ` and `σ' = conj ∘ σ ∘ conj`. The image under `σ` of the class sum of the Gram pairings of `φ g`
and `φ' g` has absolute value at most the norm of `φ` at `σ'` times the norm of `φ'` at `σ`; the
norm at `σ` is the square root of the class sum of the squared norms of the images under `σ`. -/
lemma norm_map_stdClassSum_gramForm_le {κ : InfinitePlace E → ℕ → ℕ} (K : Subgroup (Gf E n))
    [IsLevel K] (σ : ℂ ≃+* ℂ) (φ φ' : Gf E n → WeylIndex n κ → ℂ) :
    ‖σ (stdClassSum K fun g : Gf E n ↦ gramForm (φ g) (φ' g))‖ ≤
      √(stdClassSum K fun g : Gf E n ↦
          weylNormSq (((starRingAut.trans σ).trans starRingAut) ∘ φ g)) *
        √(stdClassSum K fun g : Gf E n ↦ weylNormSq (σ ∘ φ' g)) := by
  set σ' : ℂ ≃+* ℂ := (starRingAut.trans σ).trans starRingAut with hσ'
  -- The Gram matrix has integer entries, so `σ` passes through the pairing.
  have h_map (u v : WeylIndex n κ → ℂ) : σ (gramForm u v) = gramForm (σ' ∘ u) (σ ∘ v) := by
    simp [hσ', gramForm_apply, dotProduct, mulVec]
  have h_nonneg (N : ℕ) (ξ : WeylIndex n κ → ℂ) : 0 ≤ (N : ℚ)⁻¹ • weylNormSq ξ := by
    simp [Rat.smul_def, mul_nonneg]
  -- Cauchy–Schwarz for the Gram matrix at each class, then for the sum over the classes.
  have h_class (N : ℕ) (u v : WeylIndex n κ → ℂ) : ‖σ ((N : ℚ)⁻¹ • gramForm u v)‖ ≤
      √((N : ℚ)⁻¹ • weylNormSq (σ' ∘ u)) * √((N : ℚ)⁻¹ • weylNormSq (σ ∘ v)) := by
    have h_cs : ‖gramForm (σ' ∘ u) (σ ∘ v)‖ ^ 2 ≤ weylNormSq (σ ∘ v) * weylNormSq (σ' ∘ u) := by
      simpa [weylNormSq, gramForm_apply] using
        posDef_cauchy_schwarz weylGramOver_posDef (σ' ∘ u) (σ ∘ v)
    rw [← sqrt_mul (h_nonneg N _)]
    refine le_sqrt_of_sq_le ?_
    calc ‖σ ((N : ℚ)⁻¹ • gramForm u v)‖ ^ 2
      _ = (N : ℝ)⁻¹ ^ 2 * ‖gramForm (σ' ∘ u) (σ ∘ v)‖ ^ 2 := by
        simp [h_map, Rat.smul_def, mul_pow]
      _ ≤ (N : ℝ)⁻¹ ^ 2 * (weylNormSq (σ ∘ v) * weylNormSq (σ' ∘ u)) := by gcongr
      _ = _ := by simp only [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]; ring
  let m (c : DoubleCosets (stdSpace E n).Γf K) : ℕ := Nat.card (classAut (stdSpace E n).Γf K c.out)
  simp_rw [classSum, finsum_eq_sum_of_fintype, map_sum]
  calc
    _ ≤ ∑ c, √((m c : ℚ)⁻¹ • weylNormSq (σ' ∘ φ c.out)) *
          √((m c : ℚ)⁻¹ • weylNormSq (σ ∘ φ' c.out)) :=
      (norm_sum_le _ _).trans (sum_le_sum fun c _ ↦ h_class (m c) _ _)
    _ ≤ _ := sum_sqrt_mul_sqrt_le _ (fun _ ↦ h_nonneg _ _) fun _ ↦ h_nonneg _ _

end

namespace LevelPlaces

attribute [instance] fintypeChosen fintypeTwist apart

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (P : LevelPlaces E)

/-- The chosen places are pairwise distinct, and none is the conjugate of itself or of another. -/
instance isConjApart_chosenPlace : IsConjApart P.chosenPlace where
  injective := P.apart.injective.comp Sum.inl_injective
  star_ne _ _ := P.apart.star_ne (.inl _) (.inl _)

/-- The family of all places of `P`: the chosen places and the places of the twist, indexed by the
disjoint union of the two index sets. -/
abbrev placeAt : P.ChosenIndex ⊕ P.TwistIndex → FinPlace E := P.chosenPlace ⊕ᵥ P.twistPlace

/-- The set of the chosen places and the places of the twist of `P`. -/
abbrev places : Set (FinPlace E) := Set.range P.placeAt

end

section Defs

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] (S : LevelPlaces E)
  (H : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i)))) (χ : H →* ℂ)
  (κ : InfinitePlace E → ℕ → ℕ) (e : InfinitePlace E → ℤ)

/-- The space of algebraic forms of weight (κ, e) on the standard definite space on which the level
cut out by H at the places of S acts through the character χ. -/
def LevelForm : Type :=
  levelSpace (algFormRep κ e) (levelOf S.placeAt H) (χ.comp (levelOf.reduction S.placeAt H))
  deriving AddCommGroup, Module ℂ, Module ℚ

-- An algebraic form is read as a function on the finite adelic points.
instance : CoeFun (S.LevelForm H χ κ e) fun _ ↦ Gf E n → WeylIndex n κ → ℂ := ⟨(·.val.val)⟩

end Defs

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {S : LevelPlaces E}
  {H : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i)))} {χ : H →* ℂ}
  {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ}

section InnerProduct

variable (σ : ℂ ≃+* ℂ) (φ φ' : S.LevelForm H χ κ e)

/-- A form is fixed by the elements of `New.stdLevel E n`, the stabiliser of the standard lattice,
that reduce to `1` at all places of `S`. -/
lemma LevelForm.algFormRep_eq_self_of_mem {k : Gf E n} (hk : k ∈ levelOf S.placeAt ⊥) :
    algFormRep κ e k φ.val = φ.val := by
  simp [levelSpace_levelOf_apply φ.prop _ 1 (mem_levelOf.mp hk).2]

/-- A form is spherical (fixed by every element of `New.maxCompactAt n w`) at every place `w` such
that neither `w` nor `w̄` is a place of `S`. -/
lemma LevelForm.mem_sphericalAt {w : FinPlace E} (hS : w ∉ S.places.conjClosure) :
    φ.val ∈ sphericalAt (algFormRep κ e) w := by
  intro k
  simp [φ.algFormRep_eq_self_of_mem (maxCompactAt_le_levelOf hS k.2)]

/-- Evaluation at g, as a complex-linear map on the forms of the level. -/
def _root_.New.Rows.evalForm (g : Gf E n) : S.LevelForm H χ κ e →ₗ[ℂ] WeylIndex n κ → ℂ where
  toFun φ := φ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma _root_.New.Rows.apply_eq_evalForm (g : Gf E n) : φ g = Rows.evalForm g φ := rfl

/-- An algebraic form of level H on the standard definite space, viewed as a smooth form, that is, a
form with open stabiliser under right translation. -/
def LevelForm.toSmoothForm : S.LevelForm H χ κ e →ₗ[ℂ] (stdSpace E n).forms (κ, e) :=
  Submodule.subtype _

/-- For an automorphism σ of ℂ, the pairing sending (φ, φ') to σ⁻¹ of the class sum of
conj(σ φ(g))ᵀ G (σ φ'(g)), with G the integral Gram matrix of weight κ. -/
@[irreducible]
def LevelForm.innerAt :
    S.LevelForm H χ κ e →ₛₗ[(↑σ⁻¹ : ℂ →+* ℂ).comp ((starRingEnd ℂ).comp (↑σ : ℂ →+* ℂ))]
      S.LevelForm H χ κ e →ₗ[ℂ] ℂ :=
  -- the Gram form with `σ⁻¹ ∘ conj ∘ σ` as conjugation is invariant by `gramForm_map_weightRep`
  ((stdLevelIndex (levelOf S.placeAt H) : ℂ) •
      smoothPairing
        (toLinearMapₛₗ₂' ℂ (RingHom.comp ↑σ⁻¹ ((starRingEnd ℂ).comp σ)) (RingHom.id ℂ)
          (weylGramOver (κ := κ)))
        fun γ u v ↦
          σ.injective (by simpa [Int.cast_comm, toLinearMapₛₗ₂'_apply, gramForm_apply, dotProduct,
            mulVec, mul_sum] using gramForm_map_weightRep σ γ u v)).compl₂
    (toSmoothForm (χ := χ)) ∘ₛₗ toSmoothForm (χ := χ) (e := e)

/-- An element `k` of the level acts on a form, by right translation, through the character `χ`. -/
lemma LevelForm.apply_mul_eq_smul {k : Gf E n} (hk : k ∈ levelOf S.placeAt H) (g : Gf E n) :
    φ (g * k) = χ (levelOf.reduction S.placeAt H ⟨k, hk⟩) • φ g :=
  congrFun (congrArg Subtype.val (φ.2 ⟨k, hk⟩)) g

/-- For a CM field `E`, level places `S`, a subgroup `H` of the product of the groups `GL n` over
the residue fields at the places of `S`, a character `χ` and weight `(κ, e)`, let `φ φ'` be level
forms and `σ` an automorphism of `ℂ`. The pairing `innerAt σ φ φ'` equals `σ⁻¹` of the class sum at
the level `levelOf S.placeAt H`, which consists of the elements of `K₀` whose reductions at the
places of `S` lie in `H`. That class sum is the sum over double cosets `c` of the rational points
and this level in `Gf E n` of `gramForm (σ ∘ φ g_c) (σ ∘ φ' g_c) / #Aut(g_c)`. -/
lemma LevelForm.innerAt_eq_stdClassSum :
    innerAt σ φ φ' =
      σ⁻¹ (stdClassSum (levelOf S.placeAt H) fun g : Gf E n ↦ gramForm (σ ∘ φ g) (σ ∘ φ' g)) := by
  -- The pairing is the index of the level times the integral of `f`; as `f` is invariant under the
  -- level, the integral is the class sum at the level divided by this index.
  let f (g : Gf E n) : ℂ := σ⁻¹ (gramForm (σ ∘ φ g) (σ ∘ φ' g))
  have h_integral : innerAt σ φ φ' =
      stdLevelIndex (levelOf S.placeAt H) * classIntegral stdRatPoints (stdLevel E n) f := by
    have h_values (ψ : S.LevelForm H χ κ e) : (toSmoothForm ψ).val = ψ := rfl
    simp [innerAt, f, smoothPairing, h_values, toLinearMapₛₗ₂'_apply, gramForm_apply, dotProduct,
      mulVec, mul_sum, mul_comm, mul_left_comm]
  have h_left : stdRatPoints.FixesLeft f := by
    rintro _ ⟨γ, rfl⟩ g
    have h_equivariant (ψ : S.LevelForm H χ κ e) :
        ψ (stdEmbFin γ * g) = (stdSpace E n).weightRep κ e γ (ψ g) := ψ.val.2.2 γ g
    simp only [f, h_equivariant]
    exact congrArg ⇑σ⁻¹ (gramForm_map_weightRep σ γ _ _)
  -- An element `k` of the level multiplies both forms by the root of unity `χ k`.
  have h_right : levelOf S.placeAt H ≤ rightStabilizer f := by
    intro k hk g
    have h_norm : ‖σ (χ (levelOf.reduction S.placeAt H ⟨k, hk⟩))‖ = 1 :=
      (σ.toRingHom.isOfFinOrder (χ.isOfFinOrder (isMulTorsion_of_finite _))).norm_eq_one
    have h_smul (c : ℂ) (v : WeylIndex n κ → ℂ) : σ ∘ (c • v) = σ c • (σ ∘ v) :=
      funext fun i ↦ map_mul σ c (v i)
    simp [f, apply_mul_eq_smul _ hk, h_smul, ← mul_assoc, RCLike.mul_conj, h_norm]
  rw [h_integral, classIntegral_eq_inv_smul_classSum h_left h_right levelOf_le_stdLevel]
  simp [f, Rat.smul_def, map_classSum]

/-- The pairing `innerAt σ` is Hermitian for the conjugation `σ⁻¹ ∘ conj ∘ σ`. -/
lemma LevelForm.conj_innerAt : σ⁻¹ (conj (σ (φ'.innerAt σ φ))) = φ.innerAt σ φ' := by
  -- The Gram matrix is Hermitian.
  simp [innerAt_eq_stdClassSum, starRingEnd_apply, map_classSum, gramForm_apply,
    star_dotProduct_mulVec_comm weylGramOver_posDef.1]

/-- The pairing `innerAt σ` is definite: a form whose pairing with itself is zero is zero. -/
lemma LevelForm.eq_zero_of_innerAt_self (h_zero : φ.innerAt σ φ = 0) : φ = 0 := by
  -- A form is determined by its values at the representatives of the classes; if `φ` did not
  -- vanish at one of them, the class sum would be positive.
  suffices h_out : ∀ c : StdClasses (levelOf S.placeAt H), φ c.out = 0 from
    levelSpace_ext_doubleCosets Quot.out_eq h_out
  by_contra! ⟨c, hc⟩
  rw [innerAt_eq_stdClassSum, map_eq_zero] at h_zero
  have h_nonneg (g : Gf E n) : 0 ≤ gramForm (σ ∘ φ g) (σ ∘ φ g) :=
    weylGramOver_posDef.posSemidef.dotProduct_mulVec_nonneg _
  have hc_ne : σ ∘ φ c.out ≠ 0 := by simpa [_root_.funext_iff] using hc
  exact (classSum_pos h_nonneg (weylGramOver_posDef.dotProduct_mulVec_pos hc_ne)).ne' h_zero

instance : NormedAddCommGroup (S.LevelForm H χ κ e) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd :=
      { inner := (·.innerAt 1)
        conj_inner_symm := LevelForm.conj_innerAt 1
        re_inner_nonneg := fun φ ↦ by
          have h_class : RCLike.re (φ.innerAt 1 φ) =
              classSum stdRatPoints (levelOf S.placeAt H) fun g : Gf E n ↦ weylNormSq (φ g) := by
            simp [LevelForm.innerAt_eq_stdClassSum, ← Complex.reLm_coe, map_classSum,
              gramForm_apply, weylNormSq]
          rw [h_class, classSum, finsum_eq_sum_of_fintype]
          exact sum_nonneg fun c _ ↦ by simp [Rat.smul_def, mul_nonneg]
        add_left := by simp
        smul_left := by simp
        definite := LevelForm.eq_zero_of_innerAt_self 1 })

instance : InnerProductSpace ℂ (S.LevelForm H χ κ e) := .ofCore _

/-- The inner product of two forms is the class sum, at the level cut out by `H`, of the Gram
pairings of their values. -/
lemma LevelForm.inner_eq_stdClassSum :
    inner ℂ φ φ' = stdClassSum (levelOf S.placeAt H) fun g : Gf E n ↦ gramForm (φ g) (φ' g) :=
  -- by definition the inner product is `innerAt 1`
  innerAt_eq_stdClassSum 1 φ φ'

instance : FiniteDimensional ℂ (S.LevelForm H χ κ e) := finite_levelSpace_smoothFormRep

/-- The character `χ` of the finite group `H`, read on the level, has values of finite order. -/
lemma isOfFinOrder_level_char (k : levelOf S.placeAt H) :
    IsOfFinOrder (χ.comp (levelOf.reduction S.placeAt H) k) :=
  χ.isOfFinOrder (isMulTorsion_of_finite _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {S : LevelPlaces E}
  {H : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i)))} {χ : H →* ℂ} in
instance : Fact (χ.comp (levelOf.reduction S.placeAt H) =ᶠ[nhds 1] 1) := by
  -- The character is trivial on the open level of the trivial subgroup.
  refine ⟨.mono (((isOpen_levelOf (w := S.placeAt) (H := ⊥)).preimage
    continuous_subtype_val).mem_nhds (by simp)) fun k hk ↦ ?_⟩
  simp [show levelOf.reduction S.placeAt H k = 1 from Subtype.ext (mem_levelOf.mp hk).2]

/-- Let φ, ψ be forms of the level cut out by H, σ ∈ Aut ℂ, p a permutation of the infinite places
carrying the diagrams κ of φ to those of ψ, and write p also for the induced bijection of the
coordinate indices. If for all g, i we have σ(φ(g)_i) = c·a(g)·ψ(g)_{p i},
conj σ(conj φ(g)_i) = c'·a'(g)·ψ(g)_{p i} and a(g)·conj a'(g) = 1, then
σ⟨φ, φ⟩ = conj(c')·c·⟨ψ, ψ⟩. -/
lemma map_inner_self_eq {χ' : H →* ℂ} {e' : InfinitePlace E → ℤ}
    {p : InfinitePlace E ≃ InfinitePlace E} {c c' : ℂ}
    {ψ : S.LevelForm H χ' (fun τ : InfinitePlace E ↦ κ (p.symm τ)) e'} {a a' : Gf E n → ℂ}
    (hφ : ∀ (g : Gf E n) (i : WeylIndex n κ), σ (φ g i) = c * a g * ψ g (p.piCongrLeft' _ i))
    (hφ_star : ∀ (g : Gf E n) (i : WeylIndex n κ),
      star (σ (star (φ g i))) = c' * a' g * ψ g (p.piCongrLeft' _ i))
    (ha : ∀ g : Gf E n, a g * star (a' g) = 1) :
    σ (inner ℂ φ φ) = star c' * c * inner ℂ ψ ψ := by
  set f : WeylIndex n κ ≃ WeylIndex n fun τ : InfinitePlace E ↦ κ (p.symm τ) := p.piCongrLeft' _
  -- Expand both class sums in coordinates, reindexed by `f`, which preserves the Gram matrix;
  -- the factors `a g` and `star (a' g)` cancel.
  have h_star (g : Gf E n) (i : WeylIndex n κ) :
      σ (conj (φ g i)) = conj c' * conj (a' g) * conj (ψ g (f i)) := by
    simpa [f] using congrArg star (hφ_star g i)
  have h_gram (g : Gf E n) :
      σ (gramForm (φ g) (φ g)) = star c' * c * gramForm (ψ g) (ψ g) := by
    simp only [gramForm_apply, dotProduct, mulVec, mul_sum, reindex_equiv f, map_sum, map_mul,
      map_intCast, Matrix.map_apply, Pi.star_apply, RCLike.star_def,
      weylGram_eq_submatrix κ p, Matrix.submatrix_apply, hφ, h_star]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    have ha_conj : a g * conj (a' g) = 1 := ha g
    linear_combination (conj c' * c * conj (ψ g (f x)) *
      (weylGram (fun _ ↦ n) (fun τ ↦ κ (p.symm τ)) (f x) (f y) : ℂ) * ψ g (f y)) * ha_conj
  simp_rw [LevelForm.inner_eq_stdClassSum, map_classSum, mul_classSum, h_gram]

end InnerProduct

namespace LevelForm

section Sizes

variable (φ φ' : S.LevelForm H χ κ e) (σ : ℂ ≃+* ℂ) {l : ℕ} [Fact l.Prime] (j : PadicPlace l)

/-! ### Archimedean and l-adic sizes of inner products -/

/-- For σ ∈ Aut ℂ, the number ‖φ‖²_σ: the class sum of the squared Gram norms of the vectors
σ(φ(g)). -/
def normSqAt : ℝ :=
  classSum stdRatPoints (levelOf S.placeAt H) fun g : Gf E n ↦ weylNormSq (σ ∘ φ g)

/-- Cauchy–Schwarz for conjugates: for forms φ, φ' of one level and σ ∈ Aut ℂ, we have |σ⟨φ',
φ⟩| ≤ ‖φ‖_σ·‖φ'‖_{σ'}, where σ' = conj ∘ σ ∘ conj and ‖φ‖²_σ = `φ.normSqAt σ` is the class sum of
the squared Gram norms of the vectors σ(φ(g)). This is `New.norm_map_stdClassSum_gramForm_le` for
the values of the two forms. -/
lemma norm_map_inner_le :
    ‖σ (inner ℂ φ' φ)‖ ≤
      √(φ.normSqAt σ) * √(φ'.normSqAt ((starRingAut.trans σ).trans starRingAut)) := by
  rw [inner_eq_stdClassSum, mul_comm]
  exact norm_map_stdClassSum_gramForm_le (levelOf S.placeAt H) σ φ' φ

/-- Let `ρ` be the representation `New.weylRep κ e` and `G` the Gram matrix of weight `κ`. Then
`G ρ(a) = ρ(aᵀ)ᵀ G`: the matrices of `a` and of its transpose are adjoint for `G`. -/
lemma _root_.New.weylGramOver_mul_weylRep {Φ R : Type} [CommRing R] [IsDomain R] [CharZero R]
    [Fintype Φ] [DecidableEq Φ] {κ : Φ → ℕ → ℕ} (e : Φ → ℤ) (a : Φ → GL n R) :
    (weylGramOver : Matrix (WeylIndex n κ) (WeylIndex n κ) R) * weylRep κ e a =
      (weylRep κ e fun τ : Φ ↦ transposeGL (a τ))ᵀ * weylGramOver := by
  -- The transpose keeps the determinants; for the Schur matrices this is `weylGramOver_mul_schur`.
  have h_det (τ : Φ) : GeneralLinearGroup.det (transposeGL (a τ)) = GeneralLinearGroup.det (a τ) :=
    Units.ext (det_transpose _)
  simp [weylRep, Units.smul_def, h_det, weylGramOver_mul_schur]

/-- For a unitary point `g` and `j : ℂ → ℂ_l`, the component of `g⁻¹` at the embedding of `E`
induced by `j ∘ conj` at the infinite place `τ` is the transpose of the component of `g` at the one
induced by `j`. -/
lemma _root_.New.map_inv_weightEmbedding_comp_conj (g : Gf E n) (τ : InfinitePlace E) :
    GeneralLinearGroup.map (adeleExtension (weightEmbedding (j.ιₚ.comp conj) τ)) g⁻¹.val =
      transposeGL (GeneralLinearGroup.map (adeleExtension (weightEmbedding j.ιₚ τ)) g.val) := by
  have h_conj : (weightEmbedding (E := E) (j.ιₚ.comp conj) τ).comp conj = weightEmbedding j.ιₚ τ :=
    RingHom.ext (by simp [starRingEnd_apply (R := E)])
  ext i k
  -- state the entries; as `g` is unitary, those of `g⁻¹` are the conjugates of those of `gᵀ`
  change adeleExtension _ (g⁻¹.val.val i k) = adeleExtension _ (g.val.val k i)
  rw [U.inv_val_eq_conjTranspose, conjTranspose_apply, adeleExtension_star, h_conj]

/-- Let `j : ℂ → ℂ_l`. If `u` has gauge at most 1 at `g` for `j ∘ conj`, and `v` has gauge at most 1
at `g` for `j`, then the Gram pairing of `u` and `v` lies in the valuation ring `embValRing` of `j`.
-/
lemma _root_.New.gramForm_mem_embValRing {g : Gf E n} {u v : WeylIndex n κ → ℂ}
    (hu : weylGauge (ι := ⟨j.ιₚ.comp conj⟩) κ e g u ≤ 1)
    (hv : weylGauge (ι := j) κ e g v ≤ 1) : gramForm (n := n) u v ∈ embValRing (ι := j) := by
  -- For `j ∘ conj` the point `g⁻¹` acts by the transposes of the matrices `a τ` of `g` at `j`, and
  -- a matrix and its transpose are adjoint for the integral Gram matrix `G`.
  let a (τ : InfinitePlace E) : GL n ℂ_[l] :=
    GeneralLinearGroup.map (adeleExtension (weightEmbedding j.ιₚ τ)) g.val
  let G : Matrix (WeylIndex n κ) (WeylIndex n κ) ℂ_[l] := weylGramOver
  let x : WeylIndex n κ → ℂ_[l] :=
    weylRep κ e (fun τ ↦ transposeGL (a τ)) *ᵥ j.ιₚ.comp conj ∘ u
  let y : WeylIndex n κ → ℂ_[l] := weylRep κ e a⁻¹ *ᵥ j.ιₚ ∘ v
  have hx : ‖x‖ ≤ 1 := by simpa only [weylGauge, map_inv_weightEmbedding_comp_conj] using hu
  have hy : ‖y‖ ≤ 1 := by simpa [weylGauge, a, y, Pi.inv_def] using hv
  -- The two matrices cancel in the pairing, because they are adjoint for `G`.
  have h_pairing : x ⬝ᵥ G *ᵥ y = j.ιₚ (gramForm u v) :=
    calc x ⬝ᵥ G *ᵥ y
      _ = (j.ιₚ.comp conj ∘ u) ⬝ᵥ
          ((weylRep κ e fun τ ↦ transposeGL (a τ))ᵀ * G * weylRep κ e a⁻¹) *ᵥ (j.ιₚ ∘ v) := by
        simp [x, y, ← vecMul_transpose, ← dotProduct_mulVec, Matrix.mul_assoc]
      _ = (j.ιₚ.comp conj ∘ u) ⬝ᵥ G *ᵥ (j.ιₚ ∘ v) := by
        rw [← weylGramOver_mul_weylRep, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one,
          mul_one]
      -- `j` passes through the pairing, since `G` has integer entries.
      _ = j.ιₚ (gramForm u v) := by simp [G, gramForm_apply, dotProduct, mulVec]
  -- The vectors `x`, `y` and the Gram matrix have integral entries.
  change j.ιₚ (gramForm u v) ∈ NormedField.valuation.integer
  rw [← h_pairing]
  exact sum_mem fun i _ ↦ mul_mem ((norm_le_pi_norm x i).trans hx)
    (sum_mem fun k _ ↦ mul_mem (by simp [G]) ((norm_le_pi_norm y k).trans hy))

/-- The forms integral at j : ℂ → ℂ_l: the module, over the valuation ring `New.embValRing` of j, of
the forms φ whose value φ(g) has gauge `New.weylGauge` at most 1 for every g. -/
def integralForms : Submodule embValRing (S.LevelForm H χ κ e) :=
  -- the preimage of `integralFormsAt ⊤ 1` under `toSmoothForm`, with a plainer carrier
  Submodule.copy ((integralFormsAt ⊤ 1).comap (toSmoothForm.restrictScalars embValRing))
    {φ : S.LevelForm H χ κ e | ∀ g : Gf E n, weylGauge κ e g (φ g) ≤ 1} (by
      ext φ
      change _ ↔ True ∧ ∀ g : Gf E n, weylGauge κ e (g * 1) (φ g) ≤ 1
      simp)

/-- Let `j` be an `l`-adic place of ℂ, a ring map `j.ιₚ : ℂ → ℂ_l`. Let A be divisible by the orders
of all stabilisers `classAut` Γ ∩ gKg⁻¹ of the rational points U_n(E) at the level
K = `levelOf S.placeAt H`. If the level form φ is integral at j ∘ conj and φ' is integral at j
(their values have gauge `weylGauge` at most 1), then |j(A·⟨φ, φ'⟩)| ≤ 1. -/
lemma norm_nsmul_inner_le_one {A : ℕ}
    (hA : ∀ g : Gf E n, Nat.card (classAut stdRatPoints (levelOf S.placeAt H) g) ∣ A)
    (hφ : φ ∈ integralForms ⟨j.ιₚ.comp conj⟩) (hφ' : φ' ∈ integralForms j) :
    ‖j.ιₚ (A • inner ℂ φ φ')‖ ≤ 1 := by
  -- Every term of the class sum is integral, and `A` clears the weights `1 / #classAut`.
  rw [inner_eq_stdClassSum]
  exact smul_classSum_mem (embValRing (ι := j)) hA fun g ↦
    gramForm_mem_embValRing j (hφ g) (hφ' g)

end Sizes

/-! ### Coordinates of a form -/

/-- The index set of the coordinates of a form: pairs of a class and an index of the standard basis
of the Weyl module. -/
abbrev ValueIndex (H : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i))))
    (κ : InfinitePlace E → ℕ → ℕ) : Type :=
  StdClasses (levelOf S.placeAt H) × WeylIndex n κ

/-- The coordinates of the values of a form at fixed representatives of the classes. -/
def valueCoord : S.LevelForm H χ κ e →ₗ[ℂ] ValueIndex H κ → ℂ :=
  LinearMap.pi fun i ↦ LinearMap.proj i.2 ∘ₗ Rows.evalForm i.1.out

open scoped Classical Kronecker in
/-- The block diagonal matrix with one copy of the Gram matrix of the Weyl module for each class. -/
def valueMetric (H : Subgroup (∀ i : S.ChosenIndex ⊕ S.TwistIndex, GL n (ResField (S.placeAt i))))
    (κ : InfinitePlace E → ℕ → ℕ) : Matrix (ValueIndex H κ) (ValueIndex H κ) ℚ :=
  1 ⊗ₖ weylGramOver

open scoped Classical Kronecker in
/-- Over `ℂ`, `valueMetric` is the Kronecker product of the identity and the Gram matrix. -/
lemma map_valueMetric :
    ((valueMetric H κ).map (↑) : Matrix (ValueIndex H κ) (ValueIndex H κ) ℂ) =
      1 ⊗ₖ weylGramOver := by
  ext i k
  simp [valueMetric, one_apply, apply_ite (Rat.cast : ℚ → ℂ)]

lemma posDef_valueMetric :
    ((valueMetric H κ).map (↑) : Matrix (ValueIndex H κ) (ValueIndex H κ) ℂ).PosDef := by
  classical
  simpa [map_valueMetric] using PosDef.one.kronecker weylGramOver_posDef

/-- If the classes have no nontrivial automorphisms, then the class sum of the Gram pairings of the
values conjugated by σ is the pairing of the conjugated coordinates for `valueMetric`. -/
lemma stdClassSum_gramForm_eq
    (h_free : ∀ g : Gf E n, classAut stdRatPoints (levelOf S.placeAt H) g = ⊥) (σ : ℂ ≃+* ℂ)
    (φ φ' : S.LevelForm H χ κ e) :
    (stdClassSum (levelOf S.placeAt H) fun g : Gf E n ↦ gramForm (σ ∘ φ g) (σ ∘ φ' g)) =
      star (σ ∘ valueCoord φ) ⬝ᵥ (valueMetric H κ).map (↑) *ᵥ (σ ∘ valueCoord φ') := by
  -- Each class has weight one, and the Gram matrix acts on each class block by itself.
  classical
  rw [map_valueMetric, stdClassSum, classSum, finsum_eq_sum_of_fintype, dotProduct,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ ↦ ?_
  have h_apply (ψ : S.LevelForm H χ κ e) (i) : valueCoord ψ (c, i) = ψ c.out i := rfl
  simp [h_free, Fintype.sum_prod_type, h_apply, one_apply, gramForm_apply, dotProduct, mulVec]

/-- If the classes have no nontrivial automorphisms, then the inner product of forms has the block
Gram matrix `valueMetric` in the coordinates `valueCoord` (the values at representatives of the
classes). -/
lemma inner_eq_valueCoord
    (h_free : ∀ g : Gf E n, classAut stdRatPoints (levelOf S.placeAt H) g = ⊥)
    (φ φ' : S.LevelForm H χ κ e) :
    inner ℂ φ φ' = star (valueCoord φ) ⬝ᵥ (valueMetric H κ).map (↑) *ᵥ valueCoord φ' := by
  simpa [inner_eq_stdClassSum] using stdClassSum_gramForm_eq h_free 1 φ φ'

/-- If the classes have no nontrivial automorphisms, then ‖φ‖²_σ is the squared norm of the
conjugated coordinates for `valueMetric`. -/
lemma normSqAt_eq_re_valueCoord
    (h_free : ∀ g : Gf E n, classAut stdRatPoints (levelOf S.placeAt H) g = ⊥) (σ : ℂ ≃+* ℂ)
    (φ : S.LevelForm H χ κ e) :
    φ.normSqAt σ =
      (star (σ ∘ valueCoord φ) ⬝ᵥ (valueMetric H κ).map (↑) *ᵥ (σ ∘ valueCoord φ)).re := by
  rw [← stdClassSum_gramForm_eq h_free, ← Complex.reLm_coe, map_classSum]
  simp [normSqAt, weylNormSq, gramForm_apply]

end LevelForm

end LevelPlaces

end New

/-!
## Integrality and size of class sums

Arithmetic of class sums `New.classSum Γ K f = ∑ f g / #Aut g` over `Γ \ G / K`, for functions with
values in a weight module `New.WeylIndex V κ → ℂ`.
-/

namespace New.Rows

open NumberField HasFiniteType Nat

variable {E V : Type} [Field E] [CMType E] [Fintype V] [DecidableEq V] {p : ℕ} [Fact p.Prime]
  {κ : InfinitePlace E → ℕ → ℕ} {G : Type*} [Group G] [TopologicalSpace G] {Γ K : Subgroup G}
  [HasFiniteType Γ K] {B : ℝ} {f : G → WeylIndex V κ → ℂ}

/-- The gauge satisfies the ultrametric inequality. -/
lemma weylGauge_add_le_max (g : Gf E V) {e : InfinitePlace E → ℤ} [PadicPlace p]
    (ξ η : WeylIndex V κ → ℂ) :
    weylGauge κ e g (ξ + η) ≤ max (weylGauge κ e g ξ) (weylGauge κ e g η) := by
  simpa [weylGauge, Matrix.mulVec_add] using IsUltrametricDist.norm_add_le_max _ _

/-- If every `c • f x` has gauge at most one at `g` and `A` is divisible by the orders of all
stabilisers `classAut Γ K x`, then `A * c` times the class sum of `f` has gauge at most one at
`g`. -/
lemma weylGauge_classSum_le_one (g : Gf E V) {e : InfinitePlace E → ℤ} {A : ℕ} [PadicPlace p]
    (hA : ∀ x : G, Nat.card (classAut Γ K x) ∣ A) {c : ℂ}
    (hf : ∀ x : G, weylGauge κ e g (c • f x) ≤ 1) :
    weylGauge κ e g ((A * c) • classSum Γ K f) ≤ 1 := by
  -- The vectors `ξ` with `c • ξ` of gauge at most one form an additive submonoid, because the
  -- gauge is ultrametric, and `A` clears the denominators of the class sum (`smul_classSum_mem`).
  let S : AddSubmonoid (WeylIndex V κ → ℂ) :=
    { carrier := {ξ | weylGauge κ e g (c • ξ) ≤ 1}
      add_mem' := fun {ξ η} hξ hη ↦ by
        simpa [smul_add] using (weylGauge_add_le_max g (c • ξ) (c • η)).trans (max_le hξ hη)
      zero_mem' := by simp [weylGauge] }
  rw [mul_comm, mul_smul, cast_smul_eq_nsmul]
  exact smul_classSum_mem S hA hf

/-- If the conjugate by `σ` of every `f x` has norm at most `B`, that of the class sum of `f` has
norm at most `B` times the number of double cosets. -/
lemma sqrt_weylNormSq_classSum_le (σ : ℂ ≃+* ℂ) (hf : ∀ x : G, √(weylNormSq (σ ∘ f x)) ≤ B) :
    √(weylNormSq (σ ∘ classSum Γ K f)) ≤ Nat.card (DoubleCosets Γ K) * B := by
  -- Triangle inequality over the classes; the rational weight `1 / #classAut` is fixed by `σ`,
  -- comes out of the norm as a factor, and is at most one.
  calc
    _ ≤ ∑ c : DoubleCosets Γ K,
        (Nat.card (classAut Γ K c.out) : ℝ)⁻¹ * √(weylNormSq (σ ∘ f c.out)) := by
      grw [classSum, finsum_eq_sum_of_fintype, sqrt_weylNormSq_sum_le]
      simp [← algebraMap_smul ℂ]
    _ ≤ ∑ _ : DoubleCosets Γ K, 1 * B := by grw [cast_inv_le_one, hf]
    _ = _ := by simp

end New.Rows

end
