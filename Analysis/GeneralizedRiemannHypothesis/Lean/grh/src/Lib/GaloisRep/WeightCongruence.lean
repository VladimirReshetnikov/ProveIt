import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.GaloisRep.Pseudocharacter.Pseudorepresentations

/-!
# ℓ-adic models of algebraic forms and congruences that change the weight

A prime `l` and an isomorphism `ιℓ` from `ℂ` to the algebraic closure of `ℚ_[l]` are fixed. Twisting
an algebraic modular form by its weight, evaluated at the components of `g` above `l`, gives its
`l`-adic model. An ultrametric Stone–Weierstrass theorem is proved. It shows that combinations of
matrix coefficients of free weights are uniformly dense among continuous `l`-adic functions that
factor through general linear groups over one finite extension of `ℚ_[l]`.

## Main definitions and results

* `New.padicComponents`: the continuous homomorphism sending `g` to its components at the places
  above `l` induced by the embeddings `New.weightEmbedding`, one for each infinite place.
* `New.padicModel`: the `ιℓ`-semilinear map `f ↦ (g ↦ M ρ_κ'(z g)⁻¹ ιℓ(f g))`, where `ρ` is
  `New.weylRep` and `z` is `New.padicComponents`.
* `New.stoneWeierstrass_ultrametric`: a function that agrees with an element of `N` on each fibre of
  the family of all multipliers lies in the closure of `N`.
* `New.mem_uniformClosure_weylRep_coeff`: a continuous function that factors through
  `z : X → ∏ GL_N(k)`, whose entries lie in one finite extension of `ℚ_[l]`, is a uniform limit
  (`New.uniformClosure`) of combinations of matrix coefficients of free weights.
* `New.GaloisRep.exists_padicModel_hecke_contraction`: a Hecke operator at a split place, acting on
  `l`-adic functions without increasing the sup norm. It acts on the model of an eigenform by a
  fixed multiple of a coefficient of the Hecke polynomial.
* `New.padicModel_mem_uniformClosure`: the model of a form `f` is a uniform limit from the span of
  models of forms of level `K` and character `θ` whose weights are free (`New.HasNoSmallRelations`)
  at a chosen set `T` of places, if the elements of `K` trivial over `T` fix `f` and have `θ = 1`.

Notions from other files:
* `New.Space.forms`: Algebraic modular forms of weight κ on a definite space V: functions f on G_f
  with open right stabiliser and f(γg) = ρ_κ(γ)f(g) for rational γ, ρ_κ = `New.Space.weightRep`.
* `New.Weight`: for `κ : Weight E` and an infinite place `v` of `E`, `κ.1 v h` is the number of
  columns of height `h` of a Young diagram, and `κ.2 v` is an integer exponent of the determinant.
* `New.weylRep`: The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
  det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ; its rows and columns are indexed by
  `WeylIndex`/`WeylIndexFamily`, the coordinates of vectors of weight κ.
* `New.HasHeckePolyAt`: At the split place w, f is fixed by K_w, each Hecke operator T_{w,j} acts on
  f by a scalar t_j, and P = Σ(−1)^j q_w^{j(j−1)/2} t_j X^{n−j}.
* `New.ofSplitPlace`: For a split place w, the homomorphism GL_n(E_w) → G_f sending g to the unitary
  element with component g at w and 1 off w, w̄.

## Relation to the literature

Known result: Non-archimedean Stone–Weierstrass theorem for modules (localisation form). The result
concerns scalar-valued functions on a compact space over an ultrametric normed field. A continuous
function that agrees with some member of a subspace on each level set of the subspace's multipliers
lies in the closure of that subspace. Source: Dieudonné 1944; Kaplansky, The Weierstrass theorem in
fields with valuations (1950); module form as in Prolla, Approximation of Vector Valued Functions
(1977) and Topics in Functional Analysis over Valued Division Rings (1982).

Known result: Density of algebraic vectors, congruences to supercuspidal types, and limits of
eigensystems. For definite unitary groups, a form is an l-adic uniform limit of forms with very
different weight gaps at some embeddings and a prescribed character on the level, such as a wild
type. No completed cohomology or congruences modulo powers of l are used. Source: M. Emerton, V.
Paškūnas, On the density of supercuspidal points of fixed regular weight, J. Éc. polytech. Math. 7
(2020); J. Fintzen, S. W. Shin, Congruences of algebraic automorphic forms and supercuspidal
representations, Camb. J. Math. 9 (2021); Kaplansky, Proc. AMS 1 (1950).
-/

noncomputable section

/-!
## The ℓ-adic model of an algebraic form

* `New.comp_weightRep_eq_weylRep_mulVec`: on a rational point the weight acts, after `ιℓ`, through
  `New.padicComponents`.
-/

section EllAdicModel

open Matrix RingHomClass IntermediateField

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {l : ℕ} [Fact l.Prime] [PadicIso l] (κ κ' : Weight E)

/-- The homomorphism sending g to the family, over infinite places v, of its component at the place
induced by x ↦ ιΦ_v(x̄) (`New.weightEmbedding`; Φ_v is the embedding of the CM type at v, x̄ the
complex conjugate of x), read in GL_n(Q̄_l). -/
@[simps! -isSimp toFun]
def padicComponents : Gf E n →ₜ* NumberField.InfinitePlace E → GL n (PadicAlgCl l) where
  toMonoidHom := MonoidHom.pi fun v ↦
    (GeneralLinearGroup.map
        (exists_placeOfEmb_extension (weightEmbedding (toRingHom ιℓ) v)).choose).comp
      (Gf.atPlace (placeOfEmb (weightEmbedding (toRingHom ιℓ) v)))
  continuous_toFun := continuous_pi fun v ↦ (continuous_adeleExtension
    (weightEmbedding (toRingHom ιℓ) v)).generalLinearGroup_map.continuousOn.domRestrict

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The ι-semilinear map sending f to the l-adic function g ↦ M ρ_{κ'}(z(g))⁻¹ ι(f(g)), with
z = `New.padicComponents`, viewed as a function of g and a coordinate. -/
def padicModel (M : Matrix (WeylIndex n κ.1) (WeylIndexFamily (fun _ ↦ n) κ'.1) (PadicAlgCl l)) :
    (Gf E n → WeylIndexFamily (fun _ ↦ n) κ'.1 → ℂ) →ₛₗ[toRingHom ιℓ]
      Gf E n × WeylIndex n κ.1 → PadicAlgCl l where
  toFun f x := (M *ᵥ weylRep κ'.1 κ'.2 (padicComponents x.1)⁻¹ *ᵥ ιℓ ∘ f x.1) x.2
  map_add' f g := funext fun x ↦ by
    have h_add : ιℓ ∘ (f + g) x.1 = ιℓ ∘ f x.1 + ιℓ ∘ g x.1 := funext fun i ↦ map_add ιℓ _ _
    simp [mulVec_add]
  map_smul' c f := funext fun x ↦ by
    have h_smul : ιℓ ∘ (c • f) x.1 = ιℓ c • ιℓ ∘ f x.1 := funext fun i ↦ map_mul ιℓ c (f x.1 i)
    rw [h_smul, mulVec_smul, mulVec_smul]
    rfl

/-- For a rational point `γ`, applying `ιℓ` turns the action of `γ` on vectors of weight `κ` into
multiplication by the matrix `weylRep` at `padicComponents` of the finite adelic image of `γ`. -/
lemma comp_weightRep_eq_weylRep_mulVec (γ : U (stdSpace E n).J) (x : WeylIndex n κ.1 → ℂ) :
    ιℓ ∘ (stdSpace E n).weightRep κ.1 κ.2 γ x =
      weylRep κ.1 κ.2 (padicComponents (stdEmbFin γ)) *ᵥ ιℓ ∘ x := by
  -- At a rational point `γ`, the component `v` of `padicComponents` is the image of `γ` under
  -- `weightEmbedding ιℓ v`.
  have h_comp : padicComponents (stdEmbFin γ) =
      fun v ↦ GeneralLinearGroup.map (weightEmbedding (toRingHom ιℓ) v) γ := by
    ext
    -- `using!` is needed: the component is `adeleExtension` only after unfolding the chosen
    -- extension of the place, which plain `simpa` does not do
    simpa [padicComponents_toFun, Gf.atPlace] using! adeleExtension_algebraMap ..
  rw [h_comp]
  exact map_weightRep (toRingHom ιℓ) ..

/-- The values `ιℓ (f g i)` of an algebraic form `f` of weight `κ` all lie in one finite extension
`L` of `ℚ_[l]` inside its algebraic closure. -/
lemma exists_padic_field_of_form_values {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ}
    (hf : f ∈ (stdSpace E n).forms κ) :
    ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l),
      Module.Finite ℚ_[l] L ∧ ∀ (g : Gf E n) (i : WeylIndex n κ.1), ιℓ (f g i) ∈ L := by
  -- `L` is generated by the images of `E` and the values of `f` at representatives of the finitely
  -- many classes at the level `K`, which fixes `f`.
  obtain ⟨hf_open, hf_equiv⟩ := hf
  let K : Subgroup (Gf E n) := stdLevel E n ⊓ rightStabilizer f
  have hK_level : IsLevel K := ⟨inf_le_left, isOpen_stdLevel.inter hf_open⟩
  let L : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    adjoin ℚ_[l]
      ((⋃ v, .range (weightEmbedding (E := E) ιℓ v)) ∪ ⋃ c : StdClasses K, .range (ιℓ ∘ f c.out))
  refine ⟨L, ?_, fun g i ↦ ?_⟩
  · unfold L
    rw [adjoin_union, adjoin_iUnion]
    -- Each image of `E`, and each finite set of algebraic elements, generates a finite extension
    -- (both are instances).
    apply finiteDimensional_sup
  · have h_emb (v : NumberField.InfinitePlace E) (x : E) : weightEmbedding ιℓ v x ∈ L :=
      subset_adjoin _ _ (.inl (Set.mem_iUnion.mpr ⟨v, x, rfl⟩))
    have h_rep (c : StdClasses K) (j : WeylIndex n κ.1) : ιℓ (f c.out j) ∈ L :=
      subset_adjoin _ _ (.inr (Set.mem_iUnion.mpr ⟨c, j, rfl⟩))
    -- Write `g = γ c k`; `k` fixes `f` and `γ` acts by a matrix with entries in `ιℓ⁻¹ L`.
    obtain ⟨c, γ, k, rfl⟩ := exists_eq_map_mul_rep_mul stdEmbFin K (fun c ↦ c.out_eq) g
    obtain ⟨-, hk_stab⟩ := Subgroup.mem_inf.mp k.property
    rw [mem_rightStabilizer.mp hk_stab, hf_equiv, stdSpace_weightRep_apply]
    refine (L.toSubring.comap ιℓ.toRingHom).sum_mem fun j _ ↦
      mul_mem (weylRep_entry_mem _ ?_ ..) (h_rep c j)
    simpa [mem_intGL, ← map_inv] using fun v ↦ ⟨fun _ _ ↦ h_emb v _, fun _ _ ↦ h_emb v _⟩

end New

end EllAdicModel

/-!
## Density of matrix coefficients of weights

A Stone–Weierstrass theorem over an ultrametric field `k`, applied to matrix coefficients of general
linear groups. For a submodule `N` of `C(X, k)`, `N / N` is the set of its multipliers.
-/

section FreeWeightDensity

open Module Finset IsUltrametricDist Matrix MvPolynomial Submodule Fintype ContinuousMap

variable {X k : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [NormedField k]
  [IsUltrametricDist k]

/-- An ultrametric Stone–Weierstrass theorem. Suppose that for each point `a` some `d ∈ N` equals
`φ` at all points where every multiplier `u ∈ N / N` takes the same value as at `a`. Then `φ` lies
in the closure of `N`. -/
lemma New.stoneWeierstrass_ultrametric (N : Submodule k C(X, k)) (φ : C(X, k))
    (h_fibre : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ N / N, u x = u a) → φ x = d x) :
    ∀ ε > (0 : ℝ), ∃ g ∈ N, ‖φ - g‖ ≤ ε := by
  -- Suppose `φ` is at distance more than `ε` from every element of `N`. A maximal ideal `m` of the
  -- ring of bounded multipliers cuts out a set `Z` on which all multipliers are constant, so some
  -- `d ∈ N` agrees with `φ` on `Z`, and a multiplier outside `m` makes `φ - d` small everywhere.
  by_contra! ⟨ε, hε, h_far⟩
  -- `B` is the ring of the multipliers of norm at most one.
  let A : Subalgebra k C(X, k) := (N / N).toSubalgebra (by simp) fun x y hx hy z hz ↦ by
    simpa [mul_assoc] using hx _ (hy _ hz)
  let B := A.toSubring ⊓ {closedBall_openAddSubgroup _ one_pos, Submonoid.unitClosedBall _ with}
  have norm_le_one (c : B) : ‖(c : C(X, k))‖ ≤ 1 := mem_closedBall_zero_iff.mp c.property.2
  have mul_mem_N (c : B) {d : C(X, k)} (hd : d ∈ N) : (c : C(X, k)) * d ∈ N := c.property.1 d hd
  -- The `w` with `w * φ` within `ε` of `N` form a proper ideal of `B`; a maximal ideal holds it.
  obtain ⟨m, _, h_near⟩ : ∃ m : Ideal B, m.IsMaximal ∧
      ∀ w : B, ∀ g ∈ N, ‖w.1 * φ - g‖ ≤ ε → w ∈ m := by
    let N' : Submodule B C(X, k) :=
      { N.toAddSubmonoid with smul_mem' := fun c _ hd ↦ mul_mem_N c hd }
    let ball : Submodule B C(X, k) := ⟨(closedBall_openAddSubgroup _ hε).1.1,
      fun c _ ↦ by simpa using! norm_mul_le_of_le (norm_le_one c)⟩
    -- `1` is not in it, as `φ` is far from `N`
    have h_ne_top : (N' ⊔ ball).comap (LinearMap.toSpanSingleton B C(X, k) φ) ≠ ⊤ := by
      simpa [N', ball, Ideal.eq_top_iff_one, Submodule.mem_sup, ← eq_sub_iff_add_eq',
        closedBall_openAddSubgroup] using h_far
    obtain ⟨m, hm, h_le⟩ := Ideal.exists_le_maximal _ h_ne_top
    exact ⟨m, hm, fun w g hg h ↦
      h_le (mem_sup.2 ⟨g, hg, _, by simpa [ball] using! h, add_sub_cancel ..⟩)⟩
  let P := m.primeCompl
  have : Nonempty P := ⟨1⟩
  let Z : Set X := {x | ∀ f : P, 1 ≤ ‖(f : C(X, k)) x‖}
  -- By compactness, a bound for `g` on `Z` holds for `f * g` everywhere, for some `f ∉ m`.
  have h_small (g : C(X, k)) {r : ℝ} (hr : 0 < r) (hg : ∀ x ∈ Z, ‖g x‖ ≤ r) :
      ∃ f : P, ‖(f : C(X, k)) * g‖ ≤ r := by
    let U (f : P) : Set X := ((f : C(X, k)) * g) ⁻¹' Metric.closedBall 0 r
    have h_cover (x : X) : ∃ f : P, x ∈ U f := by
      by_cases hx : x ∈ Z
      · exact ⟨1, by simpa [U] using hg x hx⟩
      -- Off `Z` some `f` has size less than one, and a power of it serves.
      obtain ⟨f, hf⟩ : ∃ f : P, ‖(f : C(X, k)) x‖ < 1 := by simpa [Z] using hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < r / (‖g x‖ + 1) by positivity) hf
      use f ^ n
      suffices h_le : ‖(f : C(X, k)) x‖ ^ n * ‖g x‖ ≤ r by simpa [U] using h_le
      calc ‖(f : C(X, k)) x‖ ^ n * ‖g x‖ ≤ r / (‖g x‖ + 1) * ‖g x‖ := by grw [hn]
        _ ≤ r := by simp [field]
    have h_mono (e f : P) : U f ⊆ U (e * f) := fun x hx ↦ by
      simp [U, mul_assoc] at hx ⊢
      grw [norm_coe_le_norm, norm_le_one, one_mul, hx]
    have h_open (f : P) : IsOpen (U f) :=
      (isOpen_closedBall 0 hr.ne').preimage ((f : C(X, k)) * g).continuous
    have h_directed : Directed (· ⊆ ·) U := fun e f ↦
      ⟨e * f, by simpa [mul_comm] using h_mono f e, h_mono e f⟩
    obtain ⟨f, hf⟩ : ∃ f : P, Set.univ ⊆ U f := isCompact_univ.elim_directed_cover U h_open
      (fun x _ ↦ Set.mem_iUnion.2 (h_cover x)) h_directed
    exact ⟨f, by simpa [U, norm_le, hr.le, Set.subset_def] using hf⟩
  have h_const (u : C(X, k)) (hu : u ∈ N / N) (x : X) (hx : x ∈ Z) (a : X) (ha : a ∈ Z) :
      u x = u a := by
    -- On `Z`, `v` vanishes at `a` and is largest at some `y`. Suppose `v y ≠ 0`.
    let v : C(X, k) := u - .const X (u a)
    have hZ : IsClosed Z := isClosed_le (f := 1) (g := fun x (f : P) ↦ ‖(f : C(X, k)) x‖)
      (by fun_prop) (by fun_prop)
    obtain ⟨y, hy, h_max⟩ : ∃ y ∈ Z, IsMaxOn (fun x : X ↦ ‖v x‖) Z y :=
      hZ.isCompact.exists_isMaxOn ⟨x, hx⟩ (by fun_prop)
    refine eq_of_norm_sub_le_zero ((h_max hx).trans (not_lt.1 fun h_pos ↦ ?_))
    obtain ⟨f, hf⟩ := h_small v h_pos h_max
    -- `w = f * v / v y` vanishes at `a` and `f - w` at `y`, so both lie in `m`, while `f` does not.
    let w : B := ⟨(v y)⁻¹ • (f * v),
      A.smul_mem (mul_mem f.1.2.1 (sub_mem hu (algebraMap_mem ..))) _, by
        simpa [norm_smul, field, closedBall_openAddSubgroup]⟩
    have w_mem : w ∈ m := by_contra fun hw ↦ (ha ⟨w, hw⟩).not_gt (by simp [w, v])
    have diff_mem : f - w ∈ m := by_contra fun hw ↦
      (hy ⟨_, hw⟩).not_gt (by simp [w, mul_comm, norm_pos_iff.1 h_pos])
    exact f.property ((m.sub_mem_iff_left w_mem).mp diff_mem)
  -- Take `d` for a point of `Z` (any point if `Z` is empty).
  obtain ⟨d, hd, hφd⟩ := h_fibre (Classical.epsilon fun x ↦ x ∈ Z)
  -- On `Z` all multipliers are constant, so `φ = d` there.
  have h_bound : ∀ x ∈ Z, ‖(φ - d) x‖ ≤ ε := fun x hx ↦ by
    simp [hφd x fun u hu ↦ h_const u hu x hx _ (Classical.epsilon_spec ⟨x, hx⟩), hε.le]
  obtain ⟨f, hf⟩ := h_small (φ - d) hε h_bound
  have h_near_f : ‖(f : C(X, k)) * φ - (f : C(X, k)) * d‖ ≤ ε := by rwa [← mul_sub]
  exact f.property (h_near f _ (mul_mem_N f hd) h_near_f)

/-- An algebraically closed extension of `ℚ_[l]` has infinite degree over every finite extension. -/
lemma New.natCast_le_rank_of_isAlgClosed {l : ℕ} [Fact l.Prime] {K : Type*} [Field K]
    [Algebra ℚ_[l] K] [IsAlgClosed K] (L : IntermediateField ℚ_[l] K) [Module.Finite ℚ_[l] L]
    (N : ℕ) : N ≤ Module.rank L K := by
  by_contra! rank_lt
  have : Module.Finite L K :=
    rank_lt_aleph0_iff.mp (rank_lt.trans (Cardinal.natCast_lt_aleph0 (n := N)))
  have : Module.Finite ℚ_[l] K := .trans L K
  -- With `n` the degree, take an `(n + 1)`-th root `β` of `l`. The valuations of the norms give
  -- `(n + 1) ∣ n`.
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (l : K) (finrank ℚ_[l] K).succ_pos
  have val_eq : (finrank ℚ_[l] K + 1) * (Algebra.norm ℚ_[l] β).valuation = finrank ℚ_[l] K := by
    simpa [Algebra.norm_natCast] using congrArg (fun x ↦ (Algebra.norm ℚ_[l] x).valuation) hβ
  have h_le : (finrank ℚ_[l] K + 1 : ℤ) ≤ finrank ℚ_[l] K :=
    Int.le_of_dvd (mod_cast finrank_pos) ⟨_, val_eq.symm⟩
  lia

/-- Natural numbers `y 0, …, y (n - 1)` in which each `y j` is below `y i / (n + 1) ^ 2` for all
`i < j` give free integers `-y i` (`New.HasNoSmallRelations`: a short sum of them, with its number
of terms, determines how often each occurs). -/
lemma New.hasNoSmallRelations_of_lacunary {n : ℕ} (y : Fin n → ℕ)
    (h_gap : ∀ i : Fin n, ∀ j > i, y j < y i / (n + 1) ^ 2) :
    HasNoSmallRelations fun i : Fin n ↦ -(y i : ℤ) := by
  -- On the vectors `α` of a fixed total `d ≤ (n + 1) ^ 2`, the sum `∑ i, α i * y i` is strictly
  -- increasing for the lexicographic order.
  refine fun d hd ↦ StrictAntiOn.injOn (α := Lex _) ?_
  rintro (α : Fin n →₀ ℕ) (hα : Finsupp.degree α = d) (β : Fin n →₀ ℕ) (hβ : Finsupp.degree β = d)
    (⟨j, h_eq, h_lt⟩ : α.Lex _ _ β)
  -- Compare term by term: `α i = β i` for `i < j`, at `i = j` we gain `y j + 1`, and for `j < i`
  -- each of the `α i` summands `y i + 1` is at most `y j / (n + 1) ^ 2`.
  have h_term (i : Fin n) : α i * y i + α i + (if i = j then y j + 1 else 0) ≤
      β i * y i + β i + α i * (y j / (n + 1) ^ 2) := by
    grind [mt (Nat.mul_le_mul_left (α i) ∘ h_gap j i), mul_le_mul_left h_lt (y j)]
  have h_sum : ∑ i : Fin n, α i * y i + d + (y j + 1) ≤
      ∑ i : Fin n, β i * y i + d + d * (y j / (n + 1) ^ 2) := by
    have hα_sum : ∑ i, α i = d := by simpa [Finsupp.degree_eq_sum] using hα
    have hβ_sum : ∑ i, β i = d := by simpa [Finsupp.degree_eq_sum] using hβ
    simpa [← sum_mul, hα_sum, hβ_sum, sum_add_distrib] using sum_mono h_term
  -- The loss is at most `y j`, since `d ≤ (n + 1) ^ 2`.
  have h_loss : d * (y j / (n + 1) ^ 2) ≤ y j := by grw [hd, Nat.mul_div_le]
  simpa [Finsupp.weight_eq_sum] using
    Int.ofNat_lt.mpr (show ∑ i, α i * y i < ∑ i, β i * y i by lia)

/-- Column multiplicities `κ h` that equal `(N + 1) ^ (4 * (N - h))` for `h ≥ 2` and are at least
that for `h = 1` give a weight whose shifted entries `-∑_{j < h < N} (κ h + 1)`, `j < N`, are free
(`New.HasNoSmallRelations`). -/
lemma New.hasNoSmallRelations_of_rapid_decrease {N : ℕ} {κ : ℕ → ℕ}
    (hκ_one : (N + 1) ^ (4 * (N - 1)) ≤ κ 1)
    (hκ : ∀ h ≥ (2 : ℕ), κ h = (N + 1) ^ (4 * (N - h))) :
    HasNoSmallRelations fun j : Fin N ↦ -∑ h ∈ Ioo (j : ℕ) N, (κ h + 1) := by
  let y (j : Fin N) : ℕ := ∑ h ∈ Ioo j.val N, (κ h + 1)
  refine hasNoSmallRelations_of_lacunary y fun i j hij ↦ ?_
  -- The sum `y j` has at most `N` terms, all small against the term `κ j` of `y i`.
  have term_le (a : ℕ) (ha : a ∈ Ioo j.val N) : κ a + 1 ≤ (N + 1) ^ (4 * (N - j) - 3) := by
    rw [hκ a (by grind), Nat.succ_le_iff]
    gcongr <;> grind -- `1 < N + 1` as there is a `j : Fin N`, and `j < a`
  calc
    y j < (N + 1) * (N + 1) ^ (4 * (N - j) - 3) :=
      (sum_le_card_nsmul _ _ _ term_le).trans_lt
        (Nat.mul_lt_mul_of_pos_right (by grind [Nat.card_Ioo]) (by simp))
    _ = (N + 1) ^ (4 * (N - j)) / (N + 1) ^ 2 := by
      rw [Nat.pow_div (by grind) (by simp), ← pow_succ']
      grind
    _ ≤ (κ j + 1) / (N + 1) ^ 2 := Nat.div_le_div_right (by grind)
    _ ≤ y i / (N + 1) ^ 2 :=
      Nat.div_le_div_right (single_le_sum (f := fun h ↦ κ h + 1) (by simp) (by grind))

/-- Let `k` be an algebraically closed ultrametric normed field over `ℚ_[l]`, `X` compact, and `z` a
continuous family, over a finite set `Φ`, of invertible `N × N` matrices with entries in one finite
extension `L` of `ℚ_[l]`. A continuous `φ` factoring through `z` is a uniform limit of sums of
matrix coefficients `γ ↦ β ⬝ᵥ weylRep κ e (z γ) *ᵥ ξ` (any `e`) of weights `(κ, e)` satisfying a
freeness condition at every `τ`. The condition is that the integers
`e_j = -∑_{j < h < N} (κ τ h + 1)`, `j < N`, have no small relations (`New.HasNoSmallRelations`): if
`α`, `β` are vectors of natural numbers with `∑ α j = ∑ β j ≤ (N + 1) ^ 2` and
`∑ α j e_j = ∑ β j e_j`, then `α = β` (these `e_j`, `α`, `β` are not the `e`, `β` of the matrix
coefficients). -/
lemma New.mem_uniformClosure_weylRep_coeff {l N : ℕ} {Φ : Type} [Fact l.Prime] [Algebra ℚ_[l] k]
    [IsAlgClosed k] [Fintype Φ] [DecidableEq Φ] (z : C(X, Φ → GL (Fin N) k))
    (L : IntermediateField ℚ_[l] k) [Module.Finite ℚ_[l] L]
    (hL : ∀ (γ : X) (τ : Φ) (i j : Fin N), z γ τ i j ∈ L) {φ : X → k} (hφ : Continuous φ)
    (h_factors : φ.FactorsThrough z) :
    φ ∈ uniformClosure
        {ψ : X → k |
          ∃ (κ : Φ → ℕ → ℕ) (e : Φ → ℤ), ∃ β ξ : WeylIndex (Fin N) κ → k,
            (∀ τ : Φ, HasNoSmallRelations fun j : Fin N ↦ -∑ h ∈ Ioo ↑j N, (κ τ h + 1)) ∧
            ψ = fun γ : X ↦ β ⬝ᵥ weylRep κ e (z γ) *ᵥ ξ} := by
  -- Evaluate semi-invariant polynomials `F` at `z γ * y` for a fixed triangular `y`. The functions
  -- so obtained from the weights `κ d` span a space `S` of matrix coefficients. The first-column
  -- entries multiply `S` into itself and determine `z γ`, so `stoneWeierstrass_ultrametric`
  -- applies.
  obtain ⟨v, hv⟩ : ∃ v : Fin N → k, LinearIndependent L v :=
    exists_linearIndependent_of_le_rank (natCast_le_rank_of_isAlgClosed L N)
  let y (x : (Σ _ : Φ, Fin N) × ℕ) : k := if x.2 ≤ x.1.2 then v x.1.2 else 0
  let κ (d : Φ → ℕ) (τ : Φ) (h : ℕ) : ℕ := (N + 1) ^ (4 * (N - h)) + if h = 1 then d τ else 0
  let E (F : MatrixPoly (Σ _ : Φ, Fin N) k) : C(X, k) :=
    ⟨fun γ ↦ (rowSubst (fun τ ↦ (z γ τ).1) F).eval y, by
      simp [rowSubst, eval₂_eq, hom_bind₁]
      fun_prop⟩
  let S : Submodule k C(X, k) :=
    span k {E F | (d) (F ∈ nabla k Sigma.fst (diagramWeight (fun _ ↦ N + 1) (κ d)))}
  -- Multiplying by a variable of the first column raises `d τ` by one.
  have h_mul (τ : Φ) (a : Fin N) : E (.X (⟨τ, a⟩, 0)) ∈ S / S := by
    refine mapsTo_span (f := .mulLeft ..) ?_
    rintro _ ⟨d, F, hF, rfl⟩
    refine ⟨d + Pi.single τ 1, minor k ![⟨τ, a⟩] * F, ?_, ext (by simp [E, minor])⟩
    -- the minor adds one box in column `τ` of height one, which is `κ (d + Pi.single τ 1)`
    have h_weight : diagramWeight (fun _ ↦ N + 1) (κ (d + Pi.single τ 1)) =
        (∑ i ∈ range 1, Finsupp.single ((![⟨τ, a⟩] 0 : Σ _ : Φ, Fin N).fst, i) 1) +
          diagramWeight (fun _ ↦ N + 1) (κ d) := by
      ext ⟨σ, i⟩
      simp [diagramWeight_apply, κ, Pi.single_apply, sum_add_distrib]
      grind [a.isLt]
    rw [h_weight]
    exact SetLike.mul_mem_graded (minor_mem_nabla (Fin.forall_fin_one.2 rfl)) hF
  -- That multiplier is `∑ b, z γ τ a b * v b` at `γ`, and `v` is independent over `L`.
  have z_eq (γ δ : X) (h : ∀ u ∈ S / S, u δ = u γ) : z δ = z γ := by
    ext τ a b
    -- the multiplier of `h_mul τ a` takes the value `∑ b, z γ τ a b * v b` at `γ`
    have h_sum_L : ∑ b, (⟨_, hL δ τ a b⟩ : L) • v b = ∑ b, (⟨_, hL γ τ a b⟩ : L) • v b := by
      simpa [E, rowSubst, y, Algebra.smul_def] using h _ (h_mul τ a)
    exact Subtype.mk.inj (linearIndependent_iffₛ.mp hv _ _ h_sum_L b)
  -- The product `w` of leading minors does not vanish at `y`. Translating it by `(z γ)⁻¹` and
  -- scaling gives an element of `S` equal to `φ` on the fibre of `z` through `γ`.
  let w : MatrixPoly (Σ _ : Φ, Fin N) k :=
    ∏ τ, tableauPoly (N := N + 1) (k := κ 0 τ) k (Sigma.mk τ) fun h _ ↦ Fin.castLE h.is_le
  have w_ne : w.eval y ≠ 0 := by
    simp [w, y, tableauPoly, prod_eq_zero_iff, BlockTriangular, hv.ne_zero,
      det_of_isLowerTriangular, minor, RingHom.map_det]
  have h_local (γ : X) : ∃ b ∈ S, ∀ δ : X, (∀ u ∈ S / S, u δ = u γ) → φ δ = b δ := by
    refine ⟨E ((φ γ / w.eval y) • rowSubst (fun τ ↦ (z γ τ).1⁻¹) w), subset_span
      ⟨0, _, smul_mem _ _ (rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla), rfl⟩, fun δ h ↦ ?_⟩
    simp [E, z_eq γ δ h, h_factors (z_eq γ δ h), rowSubst_rowSubst, w_ne]
  refine mem_uniformClosure.2 fun ε hε ↦ ?_
  obtain ⟨g, hg, h_near⟩ := stoneWeierstrass_ultrametric S ⟨φ, hφ⟩ h_local ε hε
  refine ⟨g, mapsTo_span (f := coeFnLinearMap k) ?_ hg, (norm_le _ hε.le).mp h_near⟩
  -- Each generator is a matrix coefficient: expand `F` in the family `b` of the basis products of
  -- minors times the power of the determinant that the columns of height `N` contribute.
  rintro _ ⟨d, F, hF, rfl⟩
  let b (i : WeylIndex (Fin N) (κ d)) :=
    nablaBasis k _ (κ d) i * detPow k (fun _ ↦ Fin N) fun τ ↦ κ d τ N
  obtain ⟨β, hβ⟩ : F ∈ (Fintype.linearCombination k b).range :=
    nabla_le_span_nablaBasis_mul_detPow _
      (by simpa [diagramWeight, sum_range_succ, sum_add_distrib] using hF)
  refine ⟨κ d, fun τ ↦ κ d τ N, β, fun i ↦ (b i).eval y,
    fun τ ↦ hasNoSmallRelations_of_rapid_decrease (by simp [κ]) (by grind), funext ?_⟩
  -- Substituting `z γ` acts on the family `b` by the matrix
  -- `weylRep (κ d) (fun τ ↦ κ d τ N) (z γ)`.
  simp [E, b, ← hβ, weylRep, mulVec, dotProduct, mul_sum, Units.smul_def, sum_mul, mul_assoc,
    linearCombination_apply]

end FreeWeightDensity

/-! ## Approximation by forms with weights free at chosen places -/

section WeightCongruence

open NumberField IsCMField Matrix Kronecker
  Set Submodule IsUltrametricDist Finset RingHom

namespace New

variable {E : Type} [Field E] [CMType E]
  {N l : ℕ} [Fact l.Prime] [PadicIso l]
  (κ : Weight E) (w : FinPlace E) (hw : star w ≠ w) (g : GL (Fin N) (LocField w))

/-- The statement that the finite place `u` of E induced by the l-adic embedding x ↦ ιΦ_v(x̄)
attached to the infinite place `v` (`New.weightEmbedding`) is w or its conjugate w̄. -/
def InducesPlacePair (v : InfinitePlace E) : Prop :=
  let u : FinPlace E := placeOfEmb (weightEmbedding ιℓ.toRingHom v)
  u = star w ∨ u = w

/-- An embedding of `E` that induces the place `w` lies over an infinite place inducing `w` or its
conjugate. -/
lemma inducesPlacePair_mk (σ : E →+* ℂ) (h : inducedPrime σ = w) :
    InducesPlacePair w (InfinitePlace.mk σ) := by
  -- `σ` is the embedding of the CM type at its place, or the conjugate of that embedding.
  obtain hσ | hσ := Φ_mk_eq_or_star_eq σ
  · -- the place of `ιℓ ∘ Φ ∘ conj` is the conjugate of the place of `ιℓ ∘ σ`, which is `w`
    left
    show placeOfEmb (weightEmbedding ιℓ.toRingHom (InfinitePlace.mk σ)) = star w
    rw [weightEmbedding, placeOfEmb_comp_star, hσ, ← h]
  · -- `ιℓ ∘ Φ ∘ conj` is `ιℓ ∘ star Φ`, and `star Φ = σ` induces `w`
    right
    show placeOfEmb (weightEmbedding ιℓ.toRingHom (InfinitePlace.mk σ)) = w
    -- elaborator: `isConj_complexConj` is stated with `complexConj E`, which matches
    -- `starRingEnd E` only up to unfolding, hence `erw`
    erw [weightEmbedding, comp_assoc, ← isConj_complexConj]
    exact (congrArg inducedPrime hσ).trans h

/-- An element supported at `w` and its conjugate has component `1` over `τ`, unless `w` lies above
`l` and `τ` induces `w` or its conjugate. -/
lemma padicComponents_ofSplitPlace {τ : InfinitePlace E}
    (h_not_induces : ↑l ∈ w.asIdeal → ¬InducesPlacePair w τ) :
    padicComponents (ofSplitPlace hw g) τ = 1 := by
  -- The place `u` induced by `τ` contains `l`; so by hypothesis it is neither `w` nor `star w`.
  let u : FinPlace E := placeOfEmb (weightEmbedding ιℓ.toRingHom τ)
  have hl : ↑l ∈ u.asIdeal := natCast_mem_placeOfEmb _
  have h_not : ¬(u = star w ∨ u = w) := by
    intro h_ind
    -- `w` or its conjugate is `u`, so `w` contains `l` too
    have hl_w : ↑l ∈ w.asIdeal := by
      obtain h_eq | h_eq := h_ind <;> simpa [h_eq] using hl
    exact h_not_induces hl_w h_ind
  have h_ne : u ≠ w := fun h_eq ↦ h_not (.inr h_eq)
  have h_star_ne : star u ≠ w := fun h_eq ↦ h_not (.inl (by rw [← h_eq, star_star]))
  have h_one : (ofSplitPlace hw g).atPlace u = 1 := atPlace_ofSplitPlace_of_ne hw g h_ne h_star_ne
  -- `erw` is needed, as the component is the one at `u` only after unfolding `padicComponents`
  erw [padicComponents_toFun, h_one, map_one]

/-- If `v` induces `w` or its conjugate and the component of `g` over `v` is `1`, then `g` is `1`
at `w`. -/
lemma InducesPlacePair.atPlace_eq_one {v : InfinitePlace E} {g : Gf E (Fin N)}
    (h : InducesPlacePair w v) (hg : padicComponents (n := Fin N) g v = 1) :
    g.atPlace w = 1 := by
  -- The embedding of the completion is injective, so `g` is `1` at the place induced by `v`;
  -- that place is `star w` or `w`, and `g` is `1` at `star w` only if it is `1` at `w`.
  have h_at : g.atPlace (placeOfEmb (weightEmbedding ιℓ.toRingHom v)) = 1 :=
    (map_eq_one_iff _ (Units.map_injective (map_injective (RingHom.injective _)))).mp hg
  obtain h_eq | h_eq := h
  · rwa [h_eq, Gf.atPlace_star_eq_one_iff] at h_at
  · rwa [h_eq] at h_at

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- For a place `w` distinct from its conjugate and an index `j` there are a scalar `a ≠ 0`, with
(a) `a = -1` when `w` does not contain `l`, and a linear operator `T` on `l`-adic functions such
that: (b) `T` does not increase sup norms; (c) `T F = (a * ιℓ (P.coeff j)) • F` for the model
`F = padicModel κ κ' M f` if `f` has Hecke polynomial `P` at `w` and `M` intertwines weights `κ'`
and `κ` (`κ.1`: column heights) on the elements supported at `w` and its conjugate. -/
lemma GaloisRep.exists_padicModel_hecke_contraction (j : ℕ) :
    ∃ a ≠ (0 : PadicAlgCl l),
      -- (a) the normalizing constant is `-1` away from `l`
      (↑l ∉ w.asIdeal → a = -1) ∧
      ∃ T :
            (Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l) →ₗ[PadicAlgCl l]
              Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l,
        -- (b) `T` does not increase the uniform norm
        (∀ (φ : Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l) (r : ℝ),
          (∀ z : Gf E (Fin N) × WeylIndex (Fin N) κ.1, ‖φ z‖ ≤ r) →
          ∀ z : Gf E (Fin N) × WeylIndex (Fin N) κ.1, ‖T φ z‖ ≤ r) ∧
        -- (c) the model of an eigenform at `w` is an eigenvector of `T`
        ∀ {κ' : Weight E}
          {f : Gf E (Fin N) → WeylIndexFamily (fun _ : InfinitePlace E ↦ Fin N) κ'.1 → ℂ}
          (M : Matrix (WeylIndex (Fin N) κ.1) (WeylIndexFamily (fun _ ↦ Fin N) κ'.1) (PadicAlgCl l))
          (P : Polynomial ℂ),
          let F : Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l :=
            padicModel (n := Fin N) κ κ' M f
          HasHeckePolyAt f w hw P →
          (∀ g : GL (Fin N) (LocField w),
            let z : InfinitePlace E → GL (Fin N) (PadicAlgCl l) :=
              padicComponents (ofSplitPlace hw g)
            weylRep κ.1 κ.2 z * M * weylRep κ'.1 κ'.2 z⁻¹ = M) →
          T F = (a * ιℓ (P.coeff j)) • F := by
  -- `γ U` are the coset representatives of the Hecke operator at `w`. The family `Y` lists `1` and
  -- the entries of the matrices by which they act on the coefficients; `Y y` has the largest norm.
  let γ (U : Submodule _ (Fin N → ResField w)) : Gf E (Fin N) :=
    ofSplitPlace hw (transposeGL (basicCosetRep U))
  let Y : Option (Submodule (ResField w) (Fin N → ResField w) × WeylIndex (Fin N) κ.1 ×
      WeylIndex (Fin N) κ.1) → PadicAlgCl l :=
    Option.elim' 1 fun (U, a, b) ↦ weylRep κ.1 κ.2 (padicComponents (γ U)) a b
  obtain ⟨y, h_max⟩ : ∃ y, ∀ y', ‖Y y'‖ ≤ ‖Y y‖ := Finite.exists_max (fun y ↦ ‖Y y‖)
  have h_pos : 0 < ‖Y y‖ := (Units.norm_pos 1).trans_le (h_max none)
  -- The `(N - j)`-th Hecke operator on `l`-adic functions, and the integer factor of `P.coeff j`.
  let T₀ : Module.End (PadicAlgCl l) (Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l) :=
    ∑ U ∈ {U : Submodule (ResField w) (Fin N → ResField w) | Module.finrank (ResField w) U = N - j},
      .pi fun (g, i) ↦ ∑ b, Y (some (U, i, b)) • LinearMap.proj (g * γ U, b)
  let c : ℤ := if j ≤ N then (-1) ^ (N - j) * w.q ^ (N - j).choose 2 else 0
  refine ⟨-(Y y)⁻¹, by simpa using h_pos, fun hl ↦ ?_, c • -(Y y)⁻¹ • T₀, fun φ r hφ z ↦ ?_, ?_⟩
  · -- If `w ∤ l` the matrices are `1`, so the nonzero `Y y` is `1`.
    cases y with
    | none => simp [Y]
    | some _ => aesop (add simp [weylRep, padicComponents_ofSplitPlace]) (add simp Matrix.one_apply)
  · -- By the ultrametric inequality the sum obeys the bound that each of its terms obeys;
    -- the integer `c` has norm at most `1`.
    have h_sum : ‖T₀ φ z‖ ≤ ‖Y y‖ * r := by
      have hr : 0 ≤ ‖Y y‖ * r := mul_nonneg h_pos.le ((norm_nonneg _).trans (hφ z))
      simp only [T₀, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply]
      iterate 2 refine norm_sum_le_of_forall_le_of_nonneg hr fun _ _ ↦ ?_
      exact norm_mul_le_of_le (h_max _) (hφ _)
    exact (IsUltrametricDist.norm_zsmul_le ((-(Y y)⁻¹ • T₀) φ z) c).trans
      (show ‖(-(Y y)⁻¹ • T₀) φ z‖ ≤ r by simpa [field] using h_sum)
  · intro κ' f M P F ⟨h_sph, t, hP, h_eig⟩ hM
    -- As `M` intertwines, each summand of `T₀` is `padicModel` of a translate of `f`.
    have h_term (U : Submodule (ResField w) (Fin N → ResField w))
        (z : Gf E (Fin N) × WeylIndex (Fin N) κ.1) :
        ∑ b, Y (some (U, z.2, b)) * F (z.1 * γ U, b) =
        padicModel κ κ' M (rightRegular ℂ _ _ (γ U) f) z := by
      -- elaborator: the two sides match only up to unfolding after `simp`, hence `using!`
      simpa [F, padicModel, ← mulVec_mulVec] using! congrFun (congrArg (· *ᵥ _) (hM _)) _
    -- `heckeGL_eq_sum` writes the Hecke operator applied to `f` as the sum of these translates.
    have h_hecke : T₀ F = ιℓ (t (N - j)) • F := funext fun z ↦ by
      simpa [T₀, h_term, heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).mp h_sph)] using
        congrArg (padicModel κ κ' M · z) (h_eig (N - j))
    -- `P` is the Hecke polynomial, whose coefficient of degree `j` is `c` times `t (N - j)`
    have h_coeff : P.coeff j = c * t (N - j) := by rw [hP, coeff_heckePoly, Fintype.card_fin]
    simp [funext_iff, h_hecke, h_coeff, mul_left_comm, mul_assoc]

attribute [local fun_prop] Continuous.if_const

/-- A linear map that is bounded for the uniform norms and sends `S` into the span of `D` sends
uniform limits from the span of `S` to uniform limits from the span of `D`. -/
lemma map_mem_uniformClosure_of_bound {X Y k : Type} [NormedField k] {S : Set (X → k)}
    {D : Set (Y → k)} (L : (X → k) →ₗ[k] Y → k) {C : ℝ} (hC : 0 < C)
    (h_bound : ∀ (φ : X → k) (δ : ℝ), 0 < δ → (∀ x : X, ‖φ x‖ ≤ δ) → ∀ y : Y, ‖L φ y‖ ≤ C * δ)
    (hS : ∀ φ ∈ S, L φ ∈ span k D) {φ : X → k} (hφ : φ ∈ uniformClosure S) :
    L φ ∈ uniformClosure D := by
  refine mem_uniformClosure.mpr fun ε hε ↦ ?_
  obtain ⟨ψ, hψ, h_near⟩ : ∃ g ∈ span k S, ∀ x : X, ‖φ x - g x‖ ≤ ε / C :=
    mem_uniformClosure.mp hφ (ε / C) (div_pos hε hC)
  refine ⟨L ψ, (map_span_le ..).mpr hS ⟨ψ, hψ, rfl⟩, fun y ↦ ?_⟩
  calc ‖L φ y - L ψ y‖ = ‖L (φ - ψ) y‖ := by simp
    _ ≤ C * (ε / C) := h_bound _ _ (div_pos hε hC) h_near y
    _ = ε := by field

open scoped Classical in
omit [PadicIso l] in
/-- Splitting the places into `T` and its complement writes `weylRep` as a Kronecker product, up to
a reindexing `σ` of rows and columns; `p` is the pair of the restrictions of the weight `μ` to `T`
and to its complement, and the exponents `η` are split in the same way. -/
lemma exists_weylRep_eq_submatrix_kronecker (T : Set (InfinitePlace E))
    (μ : InfinitePlace E → ℕ → ℕ) {p : ({ x // x ∈ T } → ℕ → ℕ) × ({ x // x ∉ T } → ℕ → ℕ)}
    (hp : Equiv.piEquivPiSubtypeProd (fun τ : InfinitePlace E ↦ τ ∈ T) _ μ = p) :
    ∃ σ : WeylIndex (Fin N) μ ≃ WeylIndex (Fin N) p.1 × WeylIndex (Fin N) p.2,
      ∀ (η : InfinitePlace E → ℤ) (x : InfinitePlace E → GL (Fin N) (PadicAlgCl l)),
      weylRep μ η x =
        (weylRep p.1 (Equiv.piEquivPiSubtypeProd (fun τ : InfinitePlace E ↦ τ ∈ T) _ η).1
          (fun τ : { x // x ∈ T } ↦ x τ) ⊗ₖ
          weylRep p.2 (Equiv.piEquivPiSubtypeProd (fun τ : InfinitePlace E ↦ τ ∈ T) _ η).2
            (fun τ : { x // x ∉ T } ↦ x τ)).submatrix
            σ σ := by
  subst hp
  use Equiv.piEquivPiSubtypeProd (fun τ ↦ τ ∈ T) _
  simp [← ext_iff, weylRep, schur_apply_eq_prod (Φ := Subtype.{1} _), schur_apply_eq_prod (κ := μ),
    ← Fintype.prod_subtype_mul_prod_subtype (fun τ ↦ τ ∈ T), mul_smul_mul_comm]
  tauto

/-- For a character `θ` of `K` that is `1` near `1`, a form `f` of weight `κ` and `c` in
`Gf E (Fin N)`, the function `k ↦ (ιℓ (θ k), ιℓ (θ k⁻¹) • ιℓ ∘ f (c * k))` on `K` is continuous.
It is locally constant, since `f` has an open right stabiliser and `θ` is `1` near `1`. -/
private lemma continuous_character_smul_form {K : Subgroup (Gf E (Fin N))} {θ : K →* ℂ}
    (hθ : θ =ᶠ[nhds 1] 1) (f : (stdSpace E (Fin N)).forms κ) (c : Gf E (Fin N)) :
    Continuous fun k : K ↦ (ιℓ (θ k), ιℓ (θ k⁻¹) • ιℓ ∘ f.1 (c * k)) := by
  obtain ⟨hf_open, -⟩ := f.2
  have h_nhds := hθ.and (IsOpen.mem_nhds (.preimage_val hf_open) (by simp))
  exact (isLocallyConstant_of_eventually_mul
    (h_nhds.mono (by simp +contextual [← mul_assoc]))).continuous

/-- The entries of the component over `τ ∈ T` of `padicComponents x` lie in the compositum, over the
places of `T`, of the fields generated over `ℚ_[l]` by the images of `E` under `weightEmbedding`. -/
private lemma padicComponents_apply_mem_iSup_adjoin (T : Set (InfinitePlace E)) (x : Gf E (Fin N))
    (τ : T) (i j : Fin N) :
    padicComponents (l := l) x τ i j ∈
      (⨆ τ : T, .adjoin ℚ_[l] (.range (weightEmbedding ιℓ.toRingHom τ.1)) :
        IntermediateField ℚ_[l] (PadicAlgCl l)) := by
  obtain ⟨-, -, h_image, -⟩ :=
    (exists_placeOfEmb_extension (weightEmbedding ιℓ.toRingHom τ.1)).choose_spec
  exact mem_of_le_of_mem (le_iSup _ τ) (h_image _)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `K` be an open subgroup of `New.stdLevel`, `θ` a character of `K` trivial near `1`, `T` a
set of infinite places and `f` a form of weight `κ` fixed by every `d ∈ K` whose components
(`New.padicComponents`) over `T` are `1`, with `θ d = 1` for these `d`. Suppose the span of `D`
contains `padicModel κ ν M φ` for all weights `ν` equal to `κ` off `T` and free on `T`
(`New.HasNoSmallRelations`), forms `φ` of type `θ`, and matrices `M` intertwining `ν` and `κ` on
the families that are `1` over `T`. Then the `l`-adic model of `f` is a uniform limit from the span
of `D`. -/
lemma padicModel_mem_uniformClosure {K : Subgroup (Gf E (Fin N))} (hK : IsLevel K) {θ : K →* ℂ}
    (hθ : θ =ᶠ[nhds 1] 1) (T : Set (InfinitePlace E)) (f : (stdSpace E (Fin N)).forms κ)
    (h_fix : ∀ d : K, (∀ τ ∈ T, padicComponents d.val τ = 1) →
      d.val ∈ rightStabilizer f.val ∧ θ d = 1)
    {D : Set (Gf E (Fin N) × WeylIndex (Fin N) κ.1 → PadicAlgCl l)}
    (hD : ∀ ν : Weight E, ∀ φ ∈ levelSpace ((stdSpace E (Fin N)).formTranslation ν) K θ,
      -- the weight `ν` agrees with `κ` off `T`
      (∀ τ ∉ T, ν.1 τ = κ.1 τ ∧ ν.2 τ = κ.2 τ) →
      -- and is free on `T`
      (∀ τ ∈ T, HasNoSmallRelations fun j : Fin N ↦ -∑ h ∈ Finset.Ioo ↑j N, (ν.1 τ h + 1)) →
      -- `M` intertwines the actions of the families that are `1` over `T`
      ∀ M : Matrix (WeylIndex (Fin N) κ.1) (WeylIndexFamily (fun _ ↦ Fin N) ν.1) (PadicAlgCl l),
        (∀ z : InfinitePlace E → GL (Fin N) (PadicAlgCl l), (∀ τ ∈ T, z τ = 1) →
          weylRep κ.1 κ.2 z * M * weylRep ν.1 ν.2 z⁻¹ = M) →
        padicModel κ ν M φ ∈ span (PadicAlgCl l) D) :
    padicModel κ κ 1 f.val ∈ uniformClosure D := by
  classical
  -- On the class of `c` write the model of `f` at `c k` as `R c k *ᵥ Φ c k`, where `R` carries the
  -- places off `T` and `Φ` depends only on `padicComponents` over `T`. Summing over rational
  -- elements expresses the model of `f` by bounded operators `L c y` applied to the coordinates of
  -- `Φ c`. These are limits of matrix coefficients, which `L c y` sends to functions as in `hD`.
  -- `s c g` is the finite set of rational `γ` with `q c g γ = c⁻¹ γ g ∈ K`. It has as many elements
  -- as `classAut` at `c` if `c` and `g` have the same double coset, and is empty otherwise.
  let s (c g : Gf E (Fin N)) := transporter K (stdSpace E (Fin N)).embFin c g
  let q (c g : Gf E (Fin N)) (γ : s c g) : K := ⟨_, mem_transporter.1 γ.2⟩
  -- `u c` is locally constant, since elements near `1` fix `f` and have `θ = 1`.
  let u (c : Gf E (Fin N)) (k : K) : PadicAlgCl l × (WeylIndex (Fin N) κ.1 → PadicAlgCl l) :=
    (ιℓ (θ k), ιℓ (θ k⁻¹) • ιℓ ∘ f.1 (c * k))
  have hu (c : Gf E (Fin N)) : Continuous (u c) := continuous_character_smul_form κ hθ f c
  let R (c : Gf E (Fin N)) (k : K) :
      Matrix (WeylIndex (Fin N) κ.1) (WeylIndex (Fin N) κ.1) (PadicAlgCl l) :=
    (u c k).1 • weylRep κ.1 κ.2 (Tᶜ.mulIndicator (padicComponents (c * (k : Gf E (Fin N)))⁻¹))
  let Φ (c : Gf E (Fin N)) (k : K) : WeylIndex (Fin N) κ.1 → PadicAlgCl l :=
    weylRep κ.1 κ.2 (T.mulIndicator (padicComponents (c * (k : Gf E (Fin N)))⁻¹)) *ᵥ (u c k).2
  -- `L c y φ (g, i) = ∑ γ ∈ s c g, R c (q c g γ) i y * φ (q c g γ)`.
  let L (c : Gf E (Fin N)) (y : WeylIndex (Fin N) κ.1) := LinearMap.pi fun x : _ × _ ↦
    dotProductEquiv _ _ (fun γ ↦ R c (q c x.1 γ) x.2 y) ∘ₗ .funLeft _ _ (q c x.1)
  -- Each transporter contributes the value at `g`, by the equivariance of `f` under `γ`.
  obtain ⟨-, hf_equiv⟩ := f.2
  have h_term (c g : Gf E (Fin N)) (γ : s c g) :
      R c (q c g γ) *ᵥ Φ c (q c g γ) = fun i ↦ padicModel κ κ 1 f (g, i) := by
    simp +contextual [Φ, R, u, q, padicModel, mul_assoc, (hf_equiv · g),
      comp_weightRep_eq_weylRep_mulVec,
      ← (weylRep ..).map_mul, Pi.mul_def, Pi.inv_def, ((Group.isUnit _).map θ).ne_zero, mulVec_smul,
      mulIndicator, smul_mulVec]
  -- Only the class of `g` contributes at `g`, with as many terms as `s c c` has elements.
  have h_sum : padicModel κ κ 1 f.1 = ∑ c : StdClasses K,
      ((s c.out c.out).card : PadicAlgCl l)⁻¹ • ∑ y, L c.out y (Φ c.out · y) := by
    simp [L, s, ↓card_transporter, dotProduct, sum_comm, ← mulVec_apply_eq_sum, h_term,
      -mem_classAut, -MonoidHom.coe_range, funext_iff, HasFiniteType.finite_aut,
      DoubleCoset.out_eq', Nat.card_pos.ne']
  rw [h_sum]
  refine sum_mem fun c₀ _ ↦ smul_mem _ _ (sum_mem fun y _ ↦ ?_)
  generalize c₀.out = c
  obtain ⟨hR, hΦ⟩ : Continuous (fun k i ↦ R c k i y) ∧ Continuous (fun k ↦ Φ c k y) := by
    dsimp [R, Φ, weylRep, mulIndicator]
    constructor <;> fun_prop
  -- `Φ c` factors through the components `z` over `T`, by `h_fix`.
  let z : C(K, T → GL (Fin N) (PadicAlgCl l)) := .mk fun k τ ↦ padicComponents (c * k.1)⁻¹ τ
  have h_factor : (fun k ↦ Φ c k y).FactorsThrough z := fun k ↦ by
    refine (mul_left_surjective k).forall.2 fun d hd ↦ ?_
    -- `simp_all` works with `hd` and `h_fix` only
    clear * - hd h_fix
    simp_all +unfoldPartialApp [funext_iff, z, Φ, u, ← mul_assoc, (h_fix ..).1 _, mulIndicator]
  -- By `padicComponents_apply_mem_iSup_adjoin` the entries of `z` over `τ` lie in the finite
  -- extension of `ℚ_[l]` generated by an image of `E`; take the compositum over `τ`. So `Φ c · y`
  -- is a uniform limit from the span of the matrix coefficients `β ⬝ᵥ weylRep a b (z ·) *ᵥ ξ` with
  -- free shifted weights. `R` is bounded on the compact `K`, so `L c y` is bounded by the
  -- ultrametric inequality.
  obtain ⟨B, hB, hR_le⟩ := (isCompact_range hR).isBounded.exists_pos_norm_le
  refine map_mem_uniformClosure_of_bound _ hB (fun φ δ hδ hφ x ↦ ?_) ?_
    (mem_uniformClosure_weylRep_coeff z _
      (fun k τ i j ↦ padicComponents_apply_mem_iSup_adjoin T (c * k.1)⁻¹ τ i j)
      hΦ h_factor)
  · exact norm_sum_le_of_forall_le_of_nonneg (by positivity) fun γ _ ↦
      norm_mul_le_of_le ((norm_le_pi_norm (fun i ↦ R c (q c x.1 γ) i y) x.2).trans
        (hR_le _ ⟨q c x.1 γ, rfl⟩)) (hφ _)
  -- A matrix coefficient of weight `(a, b)` on `T`; let `ν` be `(a, b)` on `T` and `κ` elsewhere.
  rintro _ ⟨a, b, β, ξ, h_free, rfl⟩
  let e {α} := Equiv.piEquivPiSubtypeProd (· ∈ T) α
  let ν : Weight E := (e.symm (a, (e κ.1).2), e.symm (b, (e κ.2).2))
  obtain ⟨ρ, hρ⟩ := exists_weylRep_eq_submatrix_kronecker (N := N) (l := l) T ν.1
    (e.apply_symm_apply _)
  obtain ⟨σ, hσ⟩ := exists_weylRep_eq_submatrix_kronecker (N := N) (l := l) T κ.1 rfl
  -- `M` contracts the `T`-factor with `β`; `φ` is the form on the class of `c` made from `ξ ⊗ e_y`.
  let M : Matrix (WeylIndex (Fin N) κ.1) (WeylIndexFamily (fun _ ↦ Fin N) ν.1) (PadicAlgCl l) :=
    (vecMulVec (col 1 (σ y).1) β ⊗ₖ 1).submatrix σ ρ
  let φ : levelSpace ((stdSpace E _).formTranslation ν) K θ := deltaForm (o := ⟨hθ⟩) _ _ _ c
    (ιℓ.symm ∘ ((replicateCol _ ξ ⊗ₖ 1).submatrix ρ σ *ᵥ Pi.single y 1))
  have hM (x : _ → GL (Fin N) (PadicAlgCl l)) (hx : ∀ τ ∈ T, x τ = 1) :
      weylRep κ.1 κ.2 x * M * weylRep ν.1 ν.2 x⁻¹ = M := by
    simp [M, ν, e, *, ← Pi.one_def, ← map_mul, Pi.mul_def, ← mul_kronecker_mul]
  suffices h_eq : padicModel κ ν M φ.1 = L c y (fun k ↦ β ⬝ᵥ weylRep a b (z k) *ᵥ ξ) by
    rw [← h_eq]
    exact hD ν _ φ.2 (by simp +contextual [ν, e]) (by simpa +contextual [ν, e] using h_free) M hM
  -- Both sides are sums over `s c g` (the model of `φ` by the definition of `deltaForm`); compare
  -- term by term.
  ext
  refine (map_sum (.proj _ ∘ₛₗ padicModel _ ν M ∘ₛₗ .const ∘ₛₗ .applyₗ _) ..).trans
    ((sum_coe_sort ..).symm.trans (Finset.sum_congr rfl fun γ _ ↦ ?_))
  rw [dite_eq_left (q _ _ γ).2]
  -- First move the action of `γ` into `weylRep`, then multiply out the Kronecker products.
  simp [padicModel, Function.comp_def _ (_ ∘ _), comp_weightRep_eq_weylRep_mulVec ν, ← map_mul,
    -mulVec_single, ← (weylRep _ _ _).mul_assoc, M.mul_assoc]
  simp [M, ν, e, z, *, ← Pi.one_def, -mulVec_mulVec, mul_assoc, q, R, vecMulVec_mulVec,
    ← replicateCol_mulVec, ← mul_kronecker_mul, Matrix.one_apply]
  split <;> ring

end New

end WeightCongruence

end
