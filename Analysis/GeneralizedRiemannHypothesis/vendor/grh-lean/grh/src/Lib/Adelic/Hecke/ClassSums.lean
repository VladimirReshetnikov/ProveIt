import Lib.Adelic.Hecke.Basic
import Lib.Adelic.QuotientMeasure.Basic

/-!
# Class sums as integrals over Γ\G, orbit unfolding and means over compact subgroups

For subgroups `Γ`, `K` of a topological group `G`, `New.classSum Γ K f` is the sum of
`f g / #(Γ ∩ g K g⁻¹)` over representatives `g` of `Γ \ G / K`, where
`Γ ∩ g K g⁻¹ = New.classAut Γ K g`. The integral over `Γ \ G` with `vol K = 1` is defined from class
sums as the finite sum `New.classIntegral`, also called the mean (it is an average when `Γ = ⊥` and
`K` is the whole group). No measure theory is used. The mean `New.classIntegral` is used to average
smooth representations over compact subgroups.

## Main definitions and results

* `New.classIntegral`: the class sum at the level `rightStabilizer f ⊓ K`, divided by its index in
  `K`.
* `New.HasFiniteType`: finitely many classes and finite stabilisers, with `K` open and compact.
* `New.classSum_eq_relIndex_smul`: change of level, by double counting.
* `New.classIntegral_eq_classSum_mul`, `New.classIntegral_eq_inv_smul_classSum`: for left
  Γ-invariant f, the mean can be computed at a smaller open level that fixes f, or one whose
  conjugate by some a lies in K and fixes f (then for the right translate of f by a).
* `New.classIntegral_sum`: for smooth left Γ-invariant functions, the mean commutes with finite
  sums, additive maps and right translation.
* `New.compactMean ρ H`: the mean over H. It is invariant under H on both sides
  (`New.apply_compactMean`, `New.compactMean_apply`), projects onto the H-fixed vectors
  (`New.compactMean_mem_levelSpace`, `New.compactMean_eq_self`), and is self-adjoint for an
  invariant scalar product (`New.IsUnitary.compactMean_adjoint`).

Notions from other files:
* `Subgroup.FixesLeft`: `Γ.FixesLeft f` says that `f (γ * g) = f g` for all γ in Γ and g in G.
* `New.levelSpace π K χ`: For a representation π of G, a subgroup K and a character χ of K (by
  default trivial), the submodule of vectors v with π(k)v = χ(k)v for all k in K.

## Relation to the literature

Known result: weighted class sums for a pair (G,K), as in the theory of abstract Hecke operators and
of algebraic modular forms. They make sense for values in any rational vector space, without a Haar
measure. Source: G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions
(1971), ch. 3; B. Gross, Algebraic modular forms, Israel J. Math. 113 (1999) 61-93; M. Greenberg and
J. Voight, Lattice methods for algebraic modular forms on classical groups, arXiv 1209.2460.
-/

noncomputable section

section ClassMean

open Pointwise DoubleCoset Finset SetLike Function MulAut Subgroup IsTopologicalGroup

namespace New

section Definitions

variable {G W W' : Type*} [Group G]

/-! ### Definitions -/

/-- The subgroup of k in G with f(gk) = f(g) for all g. -/
def rightStabilizer (f : G → W) : Subgroup G where
  carrier := {k : G | ∀ g : G, f (g * k) = f g}
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  one_mem' g := by rw [mul_one]
  inv_mem' {a} ha g := by rw [← ha, inv_mul_cancel_right]

@[simp] lemma mem_rightStabilizer {f : G → W} {k : G} :
    k ∈ rightStabilizer f ↔ ∀ g : G, f (g * k) = f g := .rfl

variable (Γ K K' : Subgroup G) [AddCommGroup W] [Module ℚ W] (f : G → W) [TopologicalSpace G]

/-- The class sum of `f` at the level `K ∩ Stab f`, divided by the index of that level in `K`. It is
the finite-sum analogue, defined without measure theory, of the integral of `f` over `Γ \ G` for the
Haar measure with `vol K = 1`, and is meant for `(Γ, K)` of finite type and `f` smooth and left
`Γ`-invariant. -/
def classIntegral : W :=
  ((rightStabilizer f).relIndex K : ℚ)⁻¹ • classSum Γ (rightStabilizer f ⊓ K) f

/-- The pair `(Γ, K)` has finite type: `K` is compact and open, `Γ \ G / K` is finite and every
`Γ ∩ g K g⁻¹` is finite. -/
class HasFiniteType : Prop where
  /-- There are finitely many double cosets `Γ g K`. -/
  finite_classes : Finite (DoubleCoset.Quotient (Γ : Set G) K)
  /-- The stabiliser `Γ ∩ g K g⁻¹` of each point `g K` is finite. -/
  finite_aut (g : G) : Finite (classAut Γ K g)
  /-- `K` is open in `G`. -/
  isOpen : IsOpen (K : Set G)
  /-- `K` is compact. -/
  isCompact : IsCompact (K : Set G)

-- `open New.HasFiniteType` turns the two finiteness fields into instances and gives every finite
-- type a `Fintype` instance.
scoped[New.HasFiniteType] attribute [instance] HasFiniteType.finite_classes HasFiniteType.finite_aut
  Fintype.ofFinite

open HasFiniteType

/-! ### Smooth invariant functions, double cosets and their stabilisers -/

omit [TopologicalSpace G] in
/-- Every class in Γ\G/K' is the class of x q, with x the representative of a class in Γ\G/K and q
the representative of a coset in K/(K ∩ K'). -/
lemma surjective_doubleCoset_mk_mul :
    Surjective fun x : DoubleCosets Γ K × K ⧸ K'.subgroupOf K ↦
      DoubleCoset.mk Γ K' (x.1.out * x.2.out) := by
  refine Quot.ind fun g ↦ ?_
  -- The representative of the class of `g` is some `γ * g * k`; pair it with the coset of `k⁻¹`,
  -- whose representative is some `k⁻¹ * l` with `l ∈ K'`.
  obtain ⟨γ, hγ, k, hk, h_out⟩ : ∃ γ ∈ Γ, ∃ k ∈ K, (mk Γ K g).out = γ * g * k :=
    (eq ..).1 (out_eq' ..).symm
  lift k to K using hk
  obtain ⟨l, h_out'⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) k⁻¹
  exact ⟨(mk Γ K g, ↑k⁻¹), ((eq ..).2 ⟨γ, hγ, l, l.2, by simp [h_out, h_out', mul_assoc]⟩).symm⟩

/-- The set of left Γ-invariant functions G → W whose stabiliser under right translation is open. -/
def smoothInvariants : Set (G → W) :=
  {f : G → W | Γ.FixesLeft f ∧ IsOpen (rightStabilizer f : Set G)}

open scoped Classical in
/-- Let `u` be an injection into `G` whose range contains `Γ` (for example `id`, or the inclusion of
a group that contains `Γ`), and let `(Γ, K)` have finite type. The `γ` with `u γ ∈ Γ` and
`g⁻¹ (u γ) h ∈ K` form a finite set, with as many elements as `Γ ∩ g K g⁻¹` if `g` and `h` lie in
one class of `Γ \ G / K` and with none otherwise. -/
lemma exists_transporter {Δ : Type*} {u : Δ → G} (hu : Injective u)
    (hΓ : (Γ : Set G) ⊆ Set.range u) (K : Subgroup G) [HasFiniteType Γ K] (g h : G) :
    ∃ s : Finset Δ, (∀ γ : Δ, γ ∈ s ↔ u γ ∈ Γ ∧ g⁻¹ * u γ * h ∈ K) ∧
      #s = if mk Γ K g = mk Γ K h then Nat.card (classAut Γ K g) else 0 := by
  split_ifs with h_class
  · -- If `h = a * g * k`, the condition on `γ` says that `u γ * a` lies in `classAut Γ K g`. Take
    -- the preimage under `u` of `classAut Γ K g * a⁻¹`, which lies in `Γ`, so in the range of `u`.
    obtain ⟨a, ha, k, hk, rfl⟩ : ∃ a ∈ Γ, ∃ k ∈ K, h = a * g * k := (eq ..).1 h_class
    let A : Finset G := univ.map ⟨(classAut Γ K g).subtype, (classAut Γ K g).subtype_injective⟩
    refine ⟨(A.map (Equiv.divRight a)).preimage u hu.injOn, fun γ ↦ ?_, ?_⟩
    · simp [A, ha, hk, ← mul_assoc, mul_mem_cancel_right]
    · have h_sub : ∀ x ∈ A.map (Equiv.divRight a), x ∈ Γ := by
        simp +contextual [A, ha, mul_mem_cancel_right]
      rw [card_preimage, filter_eq_self.2 fun x hx ↦ hΓ (h_sub x hx), Nat.card_eq_fintype_card]
      simp [A]
  · -- Otherwise no `γ` qualifies, since `h = (u γ)⁻¹ * g * (g⁻¹ * u γ * h)`.
    exact ⟨∅, fun γ ↦ iff_of_false (Finset.notMem_empty γ) fun ⟨hγ, hK⟩ ↦
      h_class ((eq ..).2 ⟨(u γ)⁻¹, inv_mem hγ, g⁻¹ * u γ * h, hK, by group⟩), rfl⟩

end Definitions

open HasFiniteType

variable {G W W' : Type*} [Group G] {Γ K K' : Subgroup G} [AddCommGroup W] [Module ℚ W]
  [AddCommGroup W'] [Module ℚ W'] {f : G → W}

/-- The order of the stabiliser `classAut Γ K g` depends only on the class ΓgK. -/
lemma card_classAut_out (g : G) :
    Nat.card (classAut Γ K g) = Nat.card (classAut Γ K (DoubleCoset.mk Γ K g).out) := by
  -- The representative is some `γ * g * k`, and conjugation by `γ` matches the two stabilisers.
  obtain ⟨γ, hγ, k, hk, h_out⟩ := mk_out_eq_mul Γ K g
  have h_mem (a : G) : a ∈ classAut Γ K g ↔ conj γ a ∈ classAut Γ K (mk Γ K g).out := by
    have h_right : g⁻¹ * (a * (g * k)) ∈ K ↔ g⁻¹ * (a * g) ∈ K := by
      simp [← mul_assoc, hk, mul_mem_cancel_right]
    simp [h_out, hγ, hk, h_right, mul_assoc, mul_mem_cancel_left, mul_mem_cancel_right]
  exact Nat.card_congr ((conj γ).subtypeEquiv h_mem)

/-- The integral over `Γ \ G` of a complex function commutes with multiplication by a constant. -/
@[simp] lemma classIntegral_const_mul (β : ℂ) (f : G → ℂ) :
    classIntegral Γ K (fun g : G ↦ β * f g) = β * classIntegral Γ K f := by
  rcases eq_or_ne β 0 with rfl | hβ
  · simp [classIntegral, classSum]
  · have h_stab : rightStabilizer (fun g ↦ β * f g) = rightStabilizer f :=
      Subgroup.ext (by simp [hβ])
    rw [classIntegral, h_stab, classIntegral]
    simp only [classSum, mul_finsum, mul_smul_comm]

/-- For subgroups `Γ`, `K` of `G` and `f : G → W`, `classSum Γ K f` is the sum over double cosets
`c ∈ Γ\G/K` of `f(g_c)/#(Γ ∩ g_c K g_c⁻¹)`. The integral `classIntegral Γ K f` is the class sum at
level `K ∩ Stab f` divided by that level's index in `K`. If `K` fixes `f` under right translation,
the two are equal. -/
lemma classIntegral_eq_classSum (hK : K ≤ rightStabilizer f) :
    classIntegral Γ K f = classSum Γ K f := by
  simp [classIntegral, relIndex_eq_one.2 hK, inf_eq_right.2 hK]

omit [AddCommGroup W] [Module ℚ W] in
/-- A left `Γ`-invariant and right `K`-invariant `f` takes the same value at `g` and at the chosen
representative of the double coset `Γ g K`. -/
lemma apply_doubleCoset_out (hl : Γ.FixesLeft f) (hK : K ≤ rightStabilizer f) (g : G) :
    f (mk Γ K g).out = f g := by
  obtain ⟨γ, hγ, k, hk, h_out⟩ := mk_out_eq_mul Γ K g
  rw [h_out, hK hk, hl γ hγ]

/-! ### Finite sums over the classes -/

variable [TopologicalSpace G]

/-- If `(Γ, K)` has finite type (finitely many classes, finite stabilisers, `K` compact open),
then so has `(Γ, K')` for every open subgroup `K'` of `K`. -/
lemma HasFiniteType.of_le [H : HasFiniteType Γ K] [IsTopologicalGroup G] (h_le : K' ≤ K)
    (h_open : IsOpen (K' : Set G)) : HasFiniteType Γ K' := by
  refine ⟨?_, fun g ↦ ?_, h_open,
    H.isCompact.of_isClosed_subset (isClosed_of_isOpen _ h_open) h_le⟩
  · -- The open subgroup `K'` has finite index in the compact group `K`, and every class for `K'`
    -- comes from a class for `K` and a coset of `K'` in `K`.
    have h_index : Finite (K ⧸ K'.subgroupOf K) :=
      Nat.finite_of_card_ne_zero (H.isCompact.relIndex_ne_zero h_open)
    exact .of_surjective _ (surjective_doubleCoset_mk_mul Γ K K')
  · have h_aut : classAut Γ K' g ≤ classAut Γ K g := inf_le_inf_left Γ (comap_mono h_le)
    exact .of_injective _ (Subgroup.inclusion_injective h_aut)

/-- For a pair `(Γ, K)` of finite type (`K` compact open in the topological group `G`, `Γ \ G / K`
finite and every `Γ ∩ g K g⁻¹` finite) in which every stabiliser `classAut Γ K g = Γ ∩ g K g⁻¹` is
trivial, the class sum of the constant function `1` equals the number of double cosets `Γ g K`, as a
real number. Here `classSum Γ K f` is the sum over double cosets `c` in `Γ \ G / K` of
`f(g_c) / #(Γ ∩ g_c K g_c⁻¹)`, where `g_c` is a chosen representative of `c`. -/
lemma card_classes_eq_classSum [HasFiniteType Γ K] (h_free : ∀ g : G, classAut Γ K g = ⊥) :
    (Nat.card (DoubleCosets Γ K) : ℝ) = classSum Γ K 1 := by
  simp [classSum, finsum_eq_sum_of_fintype, h_free]

/-- Suppose `(Γ, K)` has finite type and all `Γ ∩ g K g⁻¹` are trivial, and let `f` be right
`K`-invariant with values in `A`. Then `classIntegral Γ K f`, the class sum of `f` at level
`K ∩ Stab f` divided by the index of that level in `K`, is a sum of elements of `A`, one for each
double coset in `Γ \ G / K`. -/
lemma classIntegral_mem_nsmul [HasFiniteType Γ K] (h_free : ∀ g : G, classAut Γ K g = ⊥)
    (hK : K ≤ rightStabilizer f) {A : Set W} (hA : ∀ g : G, f g ∈ A) :
    classIntegral Γ K f ∈ Nat.card (DoubleCosets Γ K) • A := by
  have h_sum : ∑ q : DoubleCosets Γ K, f q.out ∈ ∑ _q : DoubleCosets Γ K, A :=
    Set.finsetSum_mem_finsetSum univ _ _ fun q _ ↦ hA _
  simpa [classIntegral_eq_classSum hK, classSum, finsum_eq_sum_of_fintype, h_free] using h_sum

/-- The class sum of a nonnegative function that is positive at some class representative is
positive. -/
lemma classSum_pos [HasFiniteType Γ K] [PartialOrder W] [IsOrderedAddMonoid W]
    [PosSMulStrictMono ℚ W] (h_nonneg : ∀ g : G, 0 ≤ f g) {c : DoubleCosets Γ K}
    (hc : 0 < f c.out) : 0 < classSum Γ K f := by
  rw [classSum, finsum_eq_sum_of_fintype]
  have h_weight (q : DoubleCosets Γ K) : (0 : ℚ) < (Nat.card (classAut Γ K q.out) : ℚ)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact sum_pos' (fun q _ ↦ smul_nonneg (h_weight q).le (h_nonneg _))
    ⟨c, mem_univ c, smul_pos (h_weight c) hc⟩

lemma classSum_one_pos [HasFiniteType Γ K] : (0 : ℝ) < classSum Γ K 1 :=
  classSum_pos (fun _ ↦ zero_le_one) (c := mk Γ K 1) zero_lt_one

/-- Additive maps commute with class sums. -/
lemma map_classSum [HasFiniteType Γ K] {F : Type*} [FunLike F W W'] [AddMonoidHomClass F W W']
    (L : F) (f : G → W) : L (classSum Γ K f) = classSum Γ K fun g : G ↦ L (f g) := by
  simp only [classSum, finsum_eq_sum_of_fintype, map_sum, map_rat_smul]

/-- The class sum commutes with finite sums of functions. -/
lemma classSum_sum [HasFiniteType Γ K] {ι : Type*} (s : Finset ι) (f : ι → G → W) :
    classSum Γ K (fun g : G ↦ ∑ i ∈ s, f i g) = ∑ i ∈ s, classSum Γ K (f i) := by
  simpa only [classSum, finsum_eq_sum_of_fintype, smul_sum] using sum_comm

variable [IsTopologicalGroup G]

/-! ### Change of level -/

/-- For `k ∈ K`, exactly one coset `q` in `K / (L ∩ K)` has `q.out⁻¹ * k ∈ L`. -/
lemma card_filter_out_inv_mul_mem_eq_one {G : Type*} [Group G] (K L : Subgroup G)
    [Fintype (K ⧸ L.subgroupOf K)] [DecidablePred (· ∈ L)] (k : K) :
    #{q : K ⧸ L.subgroupOf K | (q.out⁻¹ * k : G) ∈ L} = 1 := by
  classical
  have h_iff (q : K ⧸ L.subgroupOf K) : (q.out⁻¹ * k : G) ∈ L ↔ q = k := by
    conv_rhs => rw [← q.out_eq', QuotientGroup.eq, mem_subgroupOf]
    rfl
  simp only [h_iff, filter_eq', mem_univ, ite_true, card_singleton]

/-- Change of level and of variable in a class sum, for `(Γ, K)` and `(Γ, K')` of finite type. Let
`L = a⁻¹ K' a ≤ K`, and let `F g` be the value of `f` at the representative of the class
`Γ (g a) K`. Then the class sum `∑ F g / #(Γ ∩ g K' g⁻¹)` over `Γ \ G / K'` is the index `[K : L]`
times the class sum of `f` over `Γ \ G / K`. -/
lemma classSum_eq_relIndex_smul [H : HasFiniteType Γ K] [J : HasFiniteType Γ K']
    {L : Subgroup G} {F : G → W} (hLK : L ≤ K) (a : G) (hL : K'.comap (conj a) = L)
    (hfF : ∀ g : G, f (mk Γ K (g * a)).out = F g) :
    classSum Γ K' F = (L.relIndex K : ℚ) • classSum Γ K f := by
  classical
  -- Double counting. `T K g h` is the finite set of `γ ∈ Γ` with `g⁻¹ * γ * h ∈ K`; it has
  -- `#classAut Γ K g` elements if `g` and `h` lie in the same class and is empty otherwise.
  subst hL
  set L : Subgroup G := K'.comap (conj a) with hL
  have h_finite : Finite (K ⧸ L.subgroupOf K) := Nat.finite_of_card_ne_zero
    (H.isCompact.relIndex_ne_zero (J.isOpen.preimage (continuous_conj a)))
  have h_transporter (U : Subgroup G) [HasFiniteType Γ U] (g h : G) : ∃ T : Finset G,
      (∀ γ : G, γ ∈ T ↔ γ ∈ Γ ∧ g⁻¹ * γ * h ∈ U) ∧
      #T = if mk Γ U g = mk Γ U h then Nat.card (classAut Γ U g) else 0 :=
    exists_transporter Γ injective_id (by simp) U g h
  choose T hT card_T using h_transporter
  -- Sort `γ ∈ T K y (x * a)` by the coset `q` of `y⁻¹ * γ * (x * a) ∈ K`; as `L = a⁻¹ * K' * a`,
  -- the part belonging to `q` is `T K' (y * q.out * a⁻¹) x`.
  have h_split (x y : G) :
      #(T K y (x * a)) = ∑ q : K ⧸ L.subgroupOf K, #(T K' (y * q.out * a⁻¹) x) :=
    calc _ = ∑ γ ∈ T K y (x * a),
            #{q : K ⧸ L.subgroupOf K | q.out⁻¹ * (y⁻¹ * γ * (x * a)) ∈ L} := by
          rw [card_eq_sum_ones]
          exact sum_congr rfl fun γ hγ ↦
            (card_filter_out_inv_mul_mem_eq_one K L ⟨_, ((hT K y (x * a) γ).1 hγ).2⟩).symm
      _ = _ := by
        simp_rw [card_eq_sum_ones]
        refine sum_comm' fun γ q ↦ ?_
        have h_mem : q.out⁻¹ * (y⁻¹ * γ * (x * a)) ∈ L → γ ∈ Γ → y⁻¹ * γ * (x * a) ∈ K :=
          fun h_mem_L _ ↦ (K.mul_mem_cancel_left (K.inv_mem q.out.2)).1 (hLK h_mem_L)
        simpa [hT, hL, mul_assoc] using h_mem
  -- Only the class of `x * a` contributes to this class sum, and its weight cancels.
  have hF (x : G) : F x = classSum Γ K fun y ↦ (#(T K y (x * a)) : ℚ) • f y := by
    rw [classSum, finsum_eq_single _ (mk Γ K (x * a))]
    · rw [card_T, out_eq', ite_eq_left rfl, inv_smul_smul₀
        (Nat.cast_ne_zero.2 Nat.card_pos.ne'), hfF]
    · exact fun c hc ↦ by simp [card_T, out_eq', hc]
  -- Likewise at level `K'`, where `g` and the representative of its class have stabilisers of
  -- the same order.
  have h_point (g y : G) : classSum Γ K' (fun x ↦ (#(T K' g x) : ℚ) • f y) = f y := by
    rw [classSum, finsum_eq_single _ (mk Γ K' g)]
    · rw [card_T, out_eq', ite_eq_left rfl, card_classAut_out g,
        inv_smul_smul₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    · exact fun c hc ↦ by simp [card_T, out_eq', hc.symm]
  -- Insert `hF` and `h_split` and sum over the classes of `K'` first: each coset `q` gives `f y`.
  calc classSum Γ K' F
      = classSum Γ K' fun x ↦ classSum Γ K fun y ↦ ∑ q : K ⧸ L.subgroupOf K,
          (#(T K' (y * q.out * a⁻¹) x) : ℚ) • f y := by
        simp only [funext hF, h_split, Nat.cast_sum, sum_smul]
    _ = classSum Γ K fun y ↦ classSum Γ K' fun x ↦ ∑ q : K ⧸ L.subgroupOf K,
          (#(T K' (y * q.out * a⁻¹) x) : ℚ) • f y := by
        -- Interchange the two finite sums over classes; their weights commute.
        simp only [classSum, finsum_eq_sum_of_fintype, smul_sum, smul_smul]
        rw [sum_comm]
        simp only [mul_left_comm]
    _ = classSum Γ K fun y ↦ ∑ _q : K ⧸ L.subgroupOf K, f y := by simp only [classSum_sum, h_point]
    _ = classSum Γ K fun y ↦ (L.relIndex K : ℚ) • f y := by
        simp [relIndex, index_eq_card, Nat.cast_smul_eq_nsmul]
    _ = (L.relIndex K : ℚ) • classSum Γ K f :=
        (map_classSum (DistribSMul.toAddMonoidHom W (L.relIndex K : ℚ)) f).symm

/-- For `K' ≤ K` with `(Γ, K)` and `(Γ, K')` of finite type, the class sum of `1` at level `K'` is
`[K : K']` times that at level `K`. -/
lemma classSum_one_of_le [HasFiniteType Γ K] [HasFiniteType Γ K'] (h_le : K' ≤ K) :
    classSum Γ K' 1 = (K'.relIndex K : ℝ) * classSum Γ K 1 := by
  rw [classSum_eq_relIndex_smul (f := 1) (F := 1) h_le 1 (Subgroup.ext (by simp)) fun _ ↦ rfl,
    Rat.smul_def, Rat.cast_natCast]

/-- For left `Γ`-invariant `f`, and `(Γ, K)`, `(Γ, K')` of finite type, the integral is
`[K : K']⁻¹` times the class sum for `K'` of `g ↦ f (g * a)`, whenever `K' ≤ K` and `a⁻¹ K' a`
(written `K'.comap (conj a)`) lies in both `K` and the right stabiliser of `f`. -/
lemma classIntegral_eq_classSum_mul [H : HasFiniteType Γ K] [J : HasFiniteType Γ K']
    (hl : Γ.FixesLeft f) (a : G) (h_le : K'.comap (conj a) ≤ rightStabilizer f ⊓ K) (hK' : K' ≤ K) :
    classIntegral Γ K f = (K'.relIndex K : ℚ)⁻¹ • classSum Γ K' fun g : G ↦ f (g * a) := by
  -- Compare the class sums at the levels `K'` and `S = Stab f ∩ K` through `L = a⁻¹ K' a ≤ S`.
  set S : Subgroup G := rightStabilizer f ⊓ K with hS
  set L : Subgroup G := K'.comap (conj a)
  have hL_open : IsOpen (L : Set G) := J.isOpen.preimage (continuous_conj a)
  have HS : HasFiniteType Γ S := H.of_le inf_le_right (isOpen_mono h_le hL_open)
  have h_sum : classSum Γ K' (fun g ↦ f (g * a)) = (L.relIndex S : ℚ) • classSum Γ S f :=
    classSum_eq_relIndex_smul h_le a rfl fun _ ↦ apply_doubleCoset_out hl inf_le_left _
  -- The indices satisfy `[K : K'] = [S : L] [K : S]`: compute the mass `classSum Γ K' 1` directly
  -- and through `S`, then cancel the positive mass at level `K`.
  have h_index : K'.relIndex K = L.relIndex S * S.relIndex K := by
    have h_mass :
        (K'.relIndex K : ℝ) * classSum Γ K 1 = L.relIndex S * S.relIndex K * classSum Γ K 1 :=
      calc _ = classSum Γ K' 1 := (classSum_one_of_le hK').symm
        _ = (L.relIndex S : ℚ) • classSum Γ S 1 := classSum_eq_relIndex_smul h_le a rfl fun _ ↦ rfl
        _ = _ := by rw [classSum_one_of_le inf_le_right, Rat.smul_def, Rat.cast_natCast, mul_assoc]
    exact_mod_cast mul_right_cancel₀ classSum_one_pos.ne' h_mass
  have h_ne : (L.relIndex S : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (HS.isCompact.relIndex_ne_zero hL_open)
  calc classIntegral Γ K f = (S.relIndex K : ℚ)⁻¹ • classSum Γ S f := by
        rw [classIntegral, hS, inf_relIndex_right]
    _ = (K'.relIndex K : ℚ)⁻¹ • classSum Γ K' fun g : G ↦ f (g * a) := by
        rw [h_index, h_sum, Nat.cast_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ h_ne]

/-- For left `Γ`-invariant `f`, the integral is `[K : K']⁻¹` times the class sum at a level
`K' ≤ K` that fixes `f`, for `(Γ, K)` and `(Γ, K')` of finite type. -/
lemma classIntegral_eq_inv_smul_classSum [HasFiniteType Γ K] [HasFiniteType Γ K']
    (hl : Γ.FixesLeft f) (h_fix : K' ≤ rightStabilizer f) (hK' : K' ≤ K) :
    classIntegral Γ K f = (K'.relIndex K : ℚ)⁻¹ • classSum Γ K' f := by
  simpa only [mul_one] using
    classIntegral_eq_classSum_mul hl 1 (fun k hk ↦ le_inf h_fix hK' (by simpa using hk)) hK'

/-! ### Additivity and translation invariance -/

/-- Let `(Γ, K)` have finite type, let the `f i` be smooth and left `Γ`-invariant, `φ i` additive
maps and `F g = ∑ i ∈ s, φ i (f i (g * a i))`. Then the integral of `F` is the sum of the `φ i` of
the integrals of the `f i`: the integral is additive, commutes with additive maps of the values and
does not change under right translation. -/
lemma classIntegral_sum [H : HasFiniteType Γ K] {ι : Type*} {F : G → W'} (s : Finset ι)
    (φ : ι → W →+ W') (a : ι → G) {f : ι → G → W} (hf : ∀ i : ι, f i ∈ smoothInvariants Γ)
    (hF : ∀ g : G, F g = ∑ i ∈ s, φ i (f i (g * a i))) :
    classIntegral Γ K F = ∑ i ∈ s, φ i (classIntegral Γ K (f i)) := by
  -- Compute every integral at one level `M`: the `k ∈ K` such that, for each `i ∈ s`, the
  -- conjugate `(a i)⁻¹ * k * a i` lies in `K` and fixes `f i`.
  have hf_left (i : ι) : Γ.FixesLeft (f i) := (hf i).1
  have hf_open (i : ι) : IsOpen (rightStabilizer (f i) : Set G) := (hf i).2
  let M : Subgroup G := K ⊓ ⨅ i : s, (rightStabilizer (f i) ⊓ K).comap (conj (a i)⁻¹)
  have hM_open : IsOpen (M : Set G) := by
    rw [coe_inf, coe_iInf]
    exact H.isOpen.inter (isOpen_iInter_of_finite fun i ↦
      ((hf_open i).inter H.isOpen).preimage (continuous_conj _))
  have hM : HasFiniteType Γ M := H.of_le inf_le_left hM_open
  have h_conj (i : ι) (hi : i ∈ s) : M.comap (conj (a i)) ≤ rightStabilizer (f i) ⊓ K :=
    fun k hk ↦ by simpa [mul_assoc] using mem_iInf.1 (Subgroup.mem_inf.1 hk).2 ⟨i, hi⟩
  have hF_left : Γ.FixesLeft F := fun γ hγ g ↦ by simp only [hF, mul_assoc, hf_left _ γ hγ]
  have hF_right : M ≤ rightStabilizer F := fun k hk g ↦ by
    rw [hF, hF]
    refine sum_congr rfl fun i hi ↦ congrArg (φ i) ?_
    have h_mem : (a i)⁻¹ * k * a i ∈ rightStabilizer (f i) :=
      (h_conj i hi (by simpa [mul_assoc] using hk)).1
    simpa [mul_assoc] using h_mem (g * a i)
  -- Class sums are finite rational combinations of values, so the `φ i` commute with them.
  rw [classIntegral_eq_inv_smul_classSum hF_left hF_right inf_le_left, funext hF, classSum_sum,
    smul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [classIntegral_eq_classSum_mul (hf_left i) (a i) (h_conj i hi) inf_le_left, map_rat_smul,
    map_classSum]

end New

end ClassMean

/-! ## Linearity of the integral over `Γ \ G`, and smooth functions -/

section Linearity

open Finset MulAut Subgroup IsTopologicalGroup

namespace New

variable {G W W' : Type*} [Group G] {Γ K : Subgroup G} [AddCommGroup W] [Module ℚ W]
  [AddCommGroup W'] [Module ℚ W'] {f : G → W} [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let `(Γ, K)` have finite type. The integral `classIntegral Γ K` over `Γ \ G` is additive on
`smoothInvariants Γ`, the left `Γ`-invariant functions fixed on the right by an open subgroup. -/
lemma classIntegral_add [HasFiniteType Γ K] {g : G → W} (hf : f ∈ smoothInvariants Γ)
    (hg : g ∈ smoothInvariants Γ) :
    classIntegral Γ K (f + g) = classIntegral Γ K f + classIntegral Γ K g := by
  -- The case of the two summands `f` and `g` of `classIntegral_sum`.
  simpa using classIntegral_sum (F := f + g) (f := ![f, g]) univ (fun _ ↦ .id W) 1
    (Fin.forall_fin_two.2 ⟨hf, hg⟩) (by simp)

/-- Let `(Γ, K)` have finite type, let `f` be smooth and left `Γ`-invariant, `L` an additive map and
`F g = L (f (g * a))`. Then the integral of `F` over `Γ \ G` is `L` of the integral of `f`: the
integral commutes with additive maps and does not change under right translation. -/
lemma classIntegral_map_mul_right [HasFiniteType Γ K] (L : W →+ W') {F : G → W'} (a : G)
    (hf : f ∈ smoothInvariants Γ) (hF : ∀ g : G, F g = L (f (g * a))) :
    classIntegral Γ K F = L (classIntegral Γ K f) := by
  -- The case of a single summand, translated by `a`, of `classIntegral_sum`.
  simpa using classIntegral_sum {a} (fun _ ↦ L) id (fun _ ↦ hf) (by simpa using hF)

variable (R : Type*) [CommSemiring R] [Module R W]

/-- The smooth functions `G → W`, those fixed under right translation by an open subgroup, as a
subrepresentation of the right regular representation. -/
def smoothFunctions : Subrepresentation (rightRegular R G W) where
  toSubmodule :=
    -- A linear combination is fixed by the intersection of the two stabilisers.
    .ofLinearComb {f : G → W | IsOpen (rightStabilizer f : Set G)} ⟨0, by simp [rightStabilizer]⟩
      fun f hf g hg _ _ ↦ isOpen_mono (H₁ := rightStabilizer f ⊓ rightStabilizer g)
        (fun k hk x ↦ by simp [hk.1 x, hk.2 x]) (hf.inter hg)
  apply_mem_toSubmodule a f hf := by
    -- The translate of `f` by `a` is fixed by the conjugate `a * rightStabilizer f * a⁻¹`.
    refine ((rightStabilizer f).comap (conj a⁻¹).toMonoidHom).isOpen_mono (fun k hk g ↦ ?_)
      (hf.preimage (continuous_conj _))
    simpa [mul_assoc] using hk (g * a)

end New

end Linearity

/-!
## Unfolding class sums along an orbit

`New.classSum_card_orbit`: under `New.HasFiniteType`, if `G` acts on a set and `H` is the stabiliser
of a point `e`, the class sum of the number of points of `Γ e ∩ g K e` is the class sum of `1` for
the preimages of `Γ` and `K` in `H`.
-/

section OrbitClassSum

open MulAction DoubleCoset Function Finset New.HasFiniteType

open Classical in
/-- Let `ι` embed `H` with image the stabiliser of `e`, let `Δ`, `L` be the preimages of `Γ`, `K`,
with `(Δ, L)` of finite type (finitely many classes, finite stabilisers, `L` compact open), and let
`ι h = a⁻¹ g k` with `a ∈ Γ`, `k ∈ K`. Among the `γ ∈ Γ` with `g⁻¹ γ (ι d) ∈ K`, those with
`γ • e = a • e` are as many as the elements of `Δ ∩ h L h⁻¹` if `Δ h L = Δ d L`, and there are none
otherwise. -/
lemma New.card_filter_smul_eq_ite_card_classAut {G H X : Type*} [Group G] [Group H] [MulAction G X]
    [TopologicalSpace H] {Γ K : Subgroup G} {Δ L : Subgroup H} [HasFiniteType Δ L] {e : X}
    {ι : H →* G} (hι : Injective ι) (he : stabilizer G e = ι.range) (hΔ : Δ = Γ.comap ι)
    (hL : L = K.comap ι) {g a k : G} {h d : H} (ha : a ∈ Γ) (hk : k ∈ K) (hh : ι h = a⁻¹ * g * k)
    {T : Finset G} (mem_T : ∀ γ : G, γ ∈ T ↔ γ ∈ Γ ∧ g⁻¹ * γ * ι d ∈ K) :
    #{γ ∈ T | a • e = γ • e} =
      if DoubleCoset.mk Δ L h = DoubleCoset.mk Δ L d then Nat.card (classAut Δ L h) else 0 := by
  -- These `γ` are the `a * ι δ` with `δ ∈ Δ` and `h⁻¹ * δ * d ∈ L`.
  obtain ⟨s, mem_s, card_s⟩ : ∃ s : Finset H, (∀ δ : H, δ ∈ s ↔ δ ∈ Δ ∧ h⁻¹ * δ * d ∈ L) ∧
      #s = if DoubleCoset.mk Δ L h = DoubleCoset.mk Δ L d then Nat.card (classAut Δ L h) else 0 :=
    exists_transporter Δ injective_id (by simp) L h d
  have mem_s_iff (δ : H) : δ ∈ s ↔ a * ι δ ∈ T := by
    have h_eq : ι (h⁻¹ * δ * d) = k⁻¹ * (g⁻¹ * (a * ι δ) * ι d) := by simp [hh, mul_assoc]
    simp only [mem_s, mem_T, hΔ, hL, Subgroup.mem_comap, h_eq,
      K.mul_mem_cancel_left (inv_mem hk), Γ.mul_mem_cancel_left ha]
  have fibre_eq :
      {γ ∈ T | a • e = γ • e} = s.map ⟨fun δ ↦ a * ι δ, (mul_right_injective a).comp hι⟩ := by
    ext γ
    obtain ⟨x, rfl⟩ : ∃ x : G, a * x = γ := mul_left_surjective a γ
    have smul_eq_iff : a • e = (a * x) • e ↔ ∃ δ : H, ι δ = x := by
      rw [mul_smul, smul_left_cancel_iff, eq_comm, ← mem_stabilizer_iff, he, MonoidHom.mem_range]
    suffices (a * x ∈ T ∧ ∃ δ : H, ι δ = x) ↔ ∃ δ : H, a * ι δ ∈ T ∧ ι δ = x by
      simpa [smul_eq_iff, mem_s_iff]
    grind
  rw [fibre_eq, card_map, card_s]

open Classical in
/-- The class sum of the function that is `#(Γ ∩ g K g⁻¹)` on the double coset `Γ g₀ K` and `0`
elsewhere is `1`: only the class of `g₀` contributes, and its weight cancels. -/
lemma New.classSum_ite_card_classAut {G : Type*} [Group G] [TopologicalSpace G] {Γ K : Subgroup G}
    [HasFiniteType Γ K] (g₀ : G) :
    classSum Γ K (fun g : G ↦ ((if DoubleCoset.mk Γ K g = DoubleCoset.mk Γ K g₀ then
      Nat.card (classAut Γ K g) else 0 : ℕ) : ℝ)) = 1 := by
  rw [classSum, finsum_eq_single _ (DoubleCoset.mk Γ K g₀) fun c hc ↦ by simp [out_eq', hc],
    out_eq', ite_eq_left rfl, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]

open Classical in
/-- Let `ι` embed `H` with image the stabiliser of `e`, let `Δ`, `L` be the preimages of `Γ`, `K`,
with `(Δ, L)` of finite type (finitely many classes, finite stabilisers, `L` compact open), and let
`S = Γ e ∩ g K e`. Let `T h` be the set of `γ ∈ Γ` with `g⁻¹ γ (ι h) ∈ K`. Then the indicator of
`S` is the sum, over the classes `d` of `(Δ, L)` and the `γ ∈ T d`, of point masses
`1 / #(Δ ∩ d L d⁻¹)` at `γ • e`. -/
lemma New.indicator_orbit_eq_sum {G H X : Type*} [Group G] [Group H] [MulAction G X]
    [TopologicalSpace H] {Γ K : Subgroup G} {Δ L : Subgroup H} [HasFiniteType Δ L] {e : X}
    {ι : H →* G} (hι : Injective ι) (he : stabilizer G e = ι.range) (hΔ : Δ = Γ.comap ι)
    (hL : L = K.comap ι) {g : G} {S : Set X}
    (hS : ∀ y : X, y ∈ S ↔ y ∈ orbit Γ e ∧ g⁻¹ • y ∈ orbit K e) {T : H → Finset G}
    (mem_T : ∀ (h : H) (γ : G), γ ∈ T h ↔ γ ∈ Γ ∧ g⁻¹ * γ * ι h ∈ K) (y : X) :
    S.indicator 1 y = ∑ d : DoubleCosets Δ L, ∑ γ ∈ T d.out,
      if y = γ • e then (Nat.card (classAut Δ L d.out) : ℝ)⁻¹ else 0 := by
  have mem_S (z : X) : z ∈ S ↔ (∃ a ∈ Γ, a • e = z) ∧ ∃ k ∈ K, k • e = g⁻¹ • z := by
    simp [hS, orbit]
  rw [Set.indicator_apply]
  split_ifs with hy
  · obtain ⟨⟨a, ha, rfl⟩, k, hk, hka⟩ := (mem_S y).1 hy
    obtain ⟨h, hh⟩ : a⁻¹ * g * k ∈ ι.range := by simp [← he, mul_smul, hka]
    -- Only the class of `h` contributes, with `#(Δ ∩ h L h⁻¹)` terms of the inverse size.
    have inner_eq (d : DoubleCosets Δ L) :
        (∑ γ ∈ T d.out, if a • e = γ • e then (Nat.card (classAut Δ L d.out) : ℝ)⁻¹ else 0) =
          if DoubleCoset.mk Δ L h = d then 1 else 0 := by
      rw [← sum_filter, sum_const, nsmul_eq_mul,
        card_filter_smul_eq_ite_card_classAut hι he hΔ hL ha hk hh (mem_T _), out_eq']
      split_ifs with hd
      · rw [card_classAut_out h, hd, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
      · simp
    simp only [inner_eq, sum_ite_eq, mem_univ, ite_true, Pi.one_apply]
  · -- If `y = γ • e` with `γ ∈ T d`, then `y ∈ S`, so every term vanishes.
    refine (sum_eq_zero fun d _ ↦ sum_eq_zero fun γ hγ ↦ ite_eq_right fun hyγ ↦ hy ?_).symm
    obtain ⟨hγΓ, hγK⟩ := (mem_T _ γ).1 hγ
    have h_fix : ι d.out • e = e := by simp [← mem_stabilizer_iff, he]
    exact (mem_S y).2 ⟨⟨γ, hγΓ, hyγ.symm⟩, _, hγK, by rw [mul_smul, mul_smul, h_fix, hyγ]⟩

open Pointwise in
/-- Let `G` act on `X`, let `ι` embed `H` with image the stabiliser of `e`, and let `Δ`, `L` be the
preimages of `Γ`, `K`; both pairs have finite type (finitely many classes, finite stabilisers,
compact open levels). Then the class sum for `(Γ, K)` of the number of points of `Γ e ∩ g K e`,
that is `∑ #(Γ e ∩ g K e) / #(Γ ∩ g K g⁻¹)` over `Γ \ G / K`, is the class sum of `1` for
`(Δ, L)`. -/
lemma New.classSum_card_orbit (G H : Type*) {X : Type*} [Group G] [Group H] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace H] {Γ K : Subgroup G} {Δ L : Subgroup H}
    [HasFiniteType Γ K] [HasFiniteType Δ L] (e : X) (ι : H →* G) (hι : Injective ι)
    (he : stabilizer G e = ι.range) (hΔ : Δ = Γ.comap ι) (hL : L = K.comap ι) :
    classSum Γ K (fun g : G ↦ ((orbit Γ e ∩ g • orbit K e).ncard : ℝ)) = classSum Δ L 1 := by
  classical
  -- By `indicator_orbit_eq_sum`, summing over all points counts `S g` as `∑ d, #(T g (ι d)) * w d`;
  -- summing that over the classes of `g` leaves `∑ d, w d`, since each `ι d` lies in one class.
  let S (g : G) : Set X := orbit Γ e ∩ g • orbit K e
  let w (d : DoubleCosets Δ L) : ℝ := (Nat.card (classAut Δ L d.out) : ℝ)⁻¹
  -- `T g h` is the set of `γ ∈ Γ` with `g⁻¹ * γ * h ∈ K`; it has `#(Γ ∩ g K g⁻¹)` elements if `g`
  -- and `h` lie in one class and is empty otherwise.
  choose T mem_T card_T using exists_transporter Γ injective_id (by simp) K
  have card_S (g : G) : ((S g).ncard : ℝ) = ∑ d : DoubleCosets Δ L, #(T g (ι d.out)) * w d :=
    calc ((S g).ncard : ℝ) = ∑' y : X, (S g).indicator 1 y := by simp [← _root_.tsum_subtype]
      _ = ∑' y : X, ∑ d : DoubleCosets Δ L, ∑ γ ∈ T g (ι d.out), if y = γ • e then w d else 0 :=
        tsum_congr <| indicator_orbit_eq_sum hι he hΔ hL
          (by simp [S, Set.mem_smul_set_iff_inv_smul_mem]) fun h ↦ mem_T g (ι h)
      _ = ∑ d : DoubleCosets Δ L, ∑ γ ∈ T g (ι d.out), w d :=
        (hasSum_sum fun d _ ↦ hasSum_sum fun γ _ ↦ hasSum_ite_eq (γ • e) _).tsum_eq
      _ = _ := by simp
  calc classSum Γ K (fun g ↦ ((S g).ncard : ℝ))
      = ∑ d : DoubleCosets Δ L, classSum Γ K (fun g ↦ (#(T g (ι d.out)) : ℝ)) * w d := by
        simp only [classSum, finsum_eq_sum_of_fintype, card_S, smul_sum, sum_mul, smul_mul_assoc]
        exact sum_comm
    _ = ∑ d : DoubleCosets Δ L, w d := by simp only [card_T, classSum_ite_card_classAut, one_mul]
    _ = classSum Δ L 1 := by simp [classSum, finsum_eq_sum_of_fintype, w, Rat.smul_def]

end OrbitClassSum

/-!
## Smooth and unitary representations and the mean over a compact subgroup

Averaging a smooth representation over a compact subgroup, without Haar measure: the mean is the
finite average `New.classIntegral` of a function that is fixed by a subgroup of finite index.

* `New.map_compactMean_of_const`: a semilinear map that is constant on the `H`-orbit of `x` takes
  the same value at the mean of `x`.
* `New.map_compactMean_of_factor`: the case of `φ ∘ ρ g` with `φ` invariant under a subgroup `K`
  and `H ⊆ (g⁻¹ K g) · Stab x`.
-/

section CompactMean

open Subgroup Topology ComplexOrder DoubleCoset Module

namespace New

section Unitary

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The sesquilinear form `B` is positive definite and invariant under `ρ`. -/
structure IsUnitary (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  /-- `B x x` is a positive real number for `x ≠ 0`. -/
  pos (x : V) (hx : x ≠ 0) : 0 < B x x
  /-- Every `ρ g` preserves `B`. -/
  map_map_eq (g : G) (x y : V) : B (ρ g x) (ρ g y) = B x y

variable {ρ} in
/-- For a `ρ`-invariant scalar product `B`, the adjoint of `ρ g` is `ρ g⁻¹`. -/
lemma IsUnitary.adjoint_eq_inv {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : IsUnitary ρ B) (g : G) (x y : V) :
    B (ρ g x) y = B x (ρ g⁻¹ y) := by
  rw [← hB.map_map_eq g x, ρ.self_inv_apply]

end Unitary

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (H : Subgroup G) {x : V} [TopologicalSpace G]

/-- The representation `ρ` is smooth: every vector is fixed by all `g` in some neighbourhood
of `1`. -/
class IsSmoothRep (ρ : Representation ℂ G V) : Prop where
  /-- The vector `x` is fixed by all `g` in some neighbourhood of `1`. -/
  eventually_fixed (x : V) : ∀ᶠ g : G in 𝓝 1, ρ g x = x

/-- A complex vector space is a rational vector space, so class integrals can take values in it. -/
local instance : Module ℚ V := .restrictScalars ℚ ℂ V

/-- There is one double coset `{1} \ G / G`. -/
instance : Unique (DoubleCoset.Quotient ({1} : Set G) (Set.univ : Set G)) where
  default := ⟦1⟧
  uniq q := q.out_eq.symm.trans ((eq (H := ⊥) (K := ⊤)).2 (by simp)).symm

variable [IsTopologicalGroup G] [IsSmoothRep ρ] [CompactSpace H]

/-- For a compact group `G` the pair `({1}, G)` has finite type. -/
instance [CompactSpace G] : HasFiniteType (⊥ : Subgroup G) ⊤ where
  finite_classes := by simp [Fintype.finite]
  finite_aut g := by simp [Fintype.finite]
  isOpen := isOpen_univ
  isCompact := isCompact_univ

/-- For `ρ` smooth and `H` compact, the function `(a, b) ↦ ρ (a⁻¹ b) x` on `H × H` lies in
`smoothInvariants ⊥`: its stabiliser under right translation is open. -/
lemma orbit_mem_smoothInvariants (x : V) :
    (fun p : H × H ↦ ρ (p.1⁻¹ * p.2) x) ∈ smoothInvariants ⊥ := by
  -- Invariance under `⊥` is trivial. The stabiliser is a subgroup, so it is open as soon as it is
  -- a neighbourhood of `1`.
  refine ⟨by simp, isOpen_of_mem_nhds _ (g := 1) ?_⟩
  let f : H × H → G := fun p ↦ p.1⁻¹ * p.2
  -- For `(k, q)` near `(1, p)` the element `(f q)⁻¹ * f (q * k)` is near `1`, so it fixes `x`.
  have h_local (p : H × H) :
      ∀ᶠ z : (H × H) × H × H in 𝓝 (1, p), ρ (f (z.2 * z.1)) x = ρ (f z.2) x := by
    have h_cont : Continuous fun z : (H × H) × H × H ↦ (f z.2)⁻¹ * f (z.2 * z.1) := by fun_prop
    filter_upwards [h_cont.tendsto' (1, p) 1 (by simp) (IsSmoothRep.eventually_fixed (ρ := ρ) x)]
      with z hz
    rwa [← ρ.inv_apply_eq_iff, ← Module.End.mul_apply, ← map_mul]
  -- By compactness one neighbourhood of `1` serves for all `q`.
  exact (isCompact_univ.eventually_forall_of_forall_eventually fun p _ ↦ h_local p).mono
    fun k hk q ↦ hk q (Set.mem_univ q)

/-- The mean of `ρ` over a compact subgroup `H`: the mean of `ρ (a⁻¹ b)` over `(a, b) ∈ H × H`.
Invariance of class integrals under right translation (`classIntegral_map_mul_right`) then gives
both sides: right translation in `a` multiplies `a⁻¹ b` on the left, and in `b` on the right. -/
@[irreducible] def compactMean : Module.End ℂ V where
  toFun x := classIntegral ⊥ ⊤ fun p : H × H ↦ ρ (p.1⁻¹ * p.2) x
  map_add' x y := by
    rw [← classIntegral_add (orbit_mem_smoothInvariants ρ H x) (orbit_mem_smoothInvariants ρ H y)]
    simp only [map_add, Pi.add_def]
  map_smul' c x := classIntegral_map_mul_right (DistribSMul.toAddMonoidHom V c) 1
    (orbit_mem_smoothInvariants ρ H x) (by simp)

variable {ρ H}
/-- An additive map `L` applied to the mean of `x` over `H` is the mean of
`L (ρ (h⁻¹ a⁻¹ b k) x)` over `(a, b) ∈ H × H`, for any `h, k ∈ H`. -/
lemma map_compactMean (L : V →+ W) (h k : H) {F : H × H → W}
    (hF : ∀ p : H × H, F p = L (ρ ((p.1 * h)⁻¹ * (p.2 * k)) x)) :
    L (compactMean ρ H x) = classIntegral ⊥ ⊤ F := by
  unfold compactMean
  exact (classIntegral_map_mul_right L (h, k) (orbit_mem_smoothInvariants ρ H x) hF).symm

/-! ### Properties of the mean -/

/-- The mean over `H` of any vector is fixed by `H`. -/
@[simp] lemma apply_compactMean {h : G} (hh : h ∈ H) (x : V) :
    ρ h (compactMean ρ H x) = compactMean ρ H x :=
  calc _ = classIntegral ⊥ ⊤ fun p : H × H ↦ ρ (p.1⁻¹ * p.2) x :=
        map_compactMean (ρ h).toAddMonoidHom ⟨h, hh⟩ 1 (by simp)
    _ = compactMean ρ H x := (map_compactMean (.id V) 1 1 (by simp)).symm

/-- Vectors in one `H`-orbit have the same mean over `H`. -/
@[simp] lemma compactMean_apply {h : G} (hh : h ∈ H) (x : V) :
    compactMean ρ H (ρ h x) = compactMean ρ H x :=
  calc _ = classIntegral ⊥ ⊤ fun p : H × H ↦ ρ (p.1⁻¹ * p.2) (ρ h x) :=
        map_compactMean (.id V) 1 1 (by simp)
    _ = compactMean ρ H x := (map_compactMean (.id V) 1 ⟨h, hh⟩ (by simp)).symm

/-- A semilinear map `φ` that takes the value `c` on the whole `H`-orbit of `x` takes the value `c`
at the mean of `x` over `H`. -/
lemma map_compactMean_of_const {σ : ℂ →+* ℂ} (φ : V →ₛₗ[σ] W) {c : W}
    (h_const : ∀ k ∈ H, φ (ρ k x) = c) : φ (compactMean ρ H x) = c :=
  calc φ (compactMean ρ H x) = classIntegral ⊥ ⊤ fun _ : H × H ↦ c :=
        map_compactMean φ.toAddMonoidHom 1 1 fun p ↦ (h_const _ (by simp [mul_mem])).symm
    _ = classSum ⊥ ⊤ fun _ : H × H ↦ c := classIntegral_eq_classSum fun k _ ↦ by simp
    -- There is a single double coset, and its weight is `1`.
    _ = c := by simp [classSum, finsum_unique]

/-- If `φ` is `K`-invariant and `H ⊆ (g⁻¹ K g) · Stab x`, then `φ ∘ ρ g` takes the same value on `x`
and on its mean over `H`. -/
lemma map_compactMean_of_factor {K : Subgroup G} {φ : V →ₗ[ℂ] W} {g : G}
    (hφ : ∀ k ∈ K, ∀ z : V, φ (ρ k z) = φ z)
    (h_factor : ∀ k ∈ H, ∃ u : G, g * u * g⁻¹ ∈ K ∧ ρ (u⁻¹ * k) x = x) :
    φ (ρ g (compactMean ρ H x)) = φ (ρ g x) := by
  refine map_compactMean_of_const (φ ∘ₗ ρ g) fun k hk ↦ ?_
  obtain ⟨u, hu, h_fix⟩ := h_factor k hk
  -- `g * k = (g * u * g⁻¹) * g * (u⁻¹ * k)`; the first factor lies in `K`, the last fixes `x`.
  calc φ (ρ g (ρ k x)) = φ (ρ (g * u * g⁻¹) (ρ g (ρ (u⁻¹ * k) x))) := by simp
    _ = φ (ρ g x) := by rw [hφ _ hu, h_fix]

/-- The mean over `H` lies in `levelSpace ρ H`, the space of `H`-fixed vectors. -/
lemma compactMean_mem_levelSpace (x : V) : compactMean ρ H x ∈ levelSpace ρ H := by simp

@[simp] lemma compactMean_eq_self (x : V) (hx : x ∈ levelSpace ρ H 1) : compactMean ρ H x = x :=
  map_compactMean_of_const .id fun k hk ↦ by simpa using hx ⟨k, hk⟩

/-- For `ρ` smooth with invariant scalar product `B`, the mean of `ρ` over a compact subgroup `H`
is self-adjoint for `B`. -/
lemma IsUnitary.compactMean_adjoint {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : IsUnitary ρ B) (x y : V) :
    B (compactMean ρ H x) y = B x (compactMean ρ H y) := by
  -- Both sides equal `B` of the two means: in each variable, `B` against an `H`-fixed vector is
  -- constant on `H`-orbits.
  have h_right : ∀ h ∈ H, B (compactMean ρ H x) (ρ h y) = B (compactMean ρ H x) y := fun h hh ↦ by
    rw [← hB.map_map_eq h _ y, apply_compactMean hh]
  have h_left : ∀ h ∈ H, B (ρ h x) (compactMean ρ H y) = B x (compactMean ρ H y) := fun h hh ↦ by
    rw [← hB.map_map_eq h x, apply_compactMean hh]
  calc B (compactMean ρ H x) y = B (compactMean ρ H x) (compactMean ρ H y) :=
        (map_compactMean_of_const (B (compactMean ρ H x)) h_right).symm
    _ = B x (compactMean ρ H y) := map_compactMean_of_const (B.flip (compactMean ρ H y)) h_left

end New

end CompactMean

/-!
## Sums over coset representatives

`New.sum_mul_out`: for `H` of finite index in `G` and `f` right `H`-invariant, the sum of `f` over
the chosen representatives `q.out` of the cosets `q` equals the sum of `f (a * q.out)`.
-/

/-- A sum over coset representatives of `G ⧸ H` of a right `H`-invariant function does not
change under left translation. -/
lemma New.sum_mul_out {G B : Type*} [Group G] [AddCommMonoid B] (H : Subgroup G) [Fintype (G ⧸ H)]
    (f : G → B) (hf : ∀ᵉ (x : G) (y ∈ H), f (x * y) = f x) (a : G) :
    ∑ q : G ⧸ H, f (a * q.out) = ∑ q : G ⧸ H, f q.out := by
  -- `q ↦ a • q` permutes the cosets, and `(a • q).out = a * q.out * y` for some `y ∈ H`.
  refine Fintype.sum_equiv (MulAction.toPerm a) _ _ fun q ↦ ?_
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H (a * q.out)
  rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul, hy, hf _ _ y.prop]

/-!
## Commutation, integrality and a bound for class sums

Under `New.HasFiniteType`, the class sum commutes with a second class sum and with multiplication by
a constant.
-/

namespace New

open HasFiniteType Finset Nat

variable {G G' W W' : Type*} [Group G] [Group G'] {Γ K : Subgroup G} {Γ' K' : Subgroup G'}
  [AddCommGroup W] [Module ℚ W] [TopologicalSpace G] [TopologicalSpace G'] [HasFiniteType Γ K]
  [HasFiniteType Γ' K'] {A : Type*} [Ring A] [Algebra ℚ A]

/-- Class sums over `Γ \ G / K` and over `Γ' \ G' / K'` commute. -/
lemma classSum_comm (f : G → G' → W) :
    classSum Γ K (fun g : G ↦ classSum Γ' K' (f g)) =
      classSum Γ' K' fun g' : G' ↦ classSum Γ K fun g : G ↦ f g g' := by
  simpa only [classSum, finsum_eq_sum_of_fintype, smul_sum, smul_smul, mul_comm] using sum_comm

lemma mul_classSum (a : A) (f : G → A) :
    a * classSum Γ K f = classSum Γ K fun g : G ↦ a * f g := by
  simp only [classSum, finsum_eq_sum_of_fintype, mul_sum, mul_smul_comm]

@[simp] lemma classSum_mul (a : A) (f : G → A) :
    classSum Γ K f * a = classSum Γ K fun g : G ↦ f g * a := by
  simp only [classSum, finsum_eq_sum_of_fintype, sum_mul, smul_mul_assoc]

/-- Integrality of class sums: if the order of every stabiliser `Γ ∩ g K g⁻¹` divides `M` and `f`
takes values in the additive submonoid `p`, then `M` times the class sum of `f` lies in `p`. -/
lemma smul_classSum_mem {S : Type*} [SetLike S W] [AddSubmonoidClass S W] (p : S) {M : ℕ}
    (hM : ∀ g : G, Nat.card (classAut Γ K g) ∣ M) {f : G → W} (hf : ∀ g : G, f g ∈ p) :
    M • classSum Γ K f ∈ p := by
  simp only [classSum, finsum_eq_sum_of_fintype, smul_sum]
  refine sum_mem fun c _ ↦ ?_
  -- The weight `M / #classAut` of each class is a natural number.
  rw [← cast_smul_eq_nsmul ℚ, smul_smul, ← div_eq_mul_inv, ← cast_div_charZero (hM _)]
  simpa only [cast_smul_eq_nsmul] using nsmul_mem (hf _) _

/-- If the real function `f` is bounded above by `C ≥ 0`, its class sum is at most the number of
double cosets `Γ \ G / K` times `C`, since every weight `1 / #(Γ ∩ g K g⁻¹)` is at most `1`. -/
lemma classSum_le_card_mul {f : G → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ g : G, f g ≤ C) :
    classSum Γ K f ≤ Nat.card (DoubleCosets Γ K) * C :=
  calc classSum Γ K f = ∑ c : DoubleCosets Γ K, (Nat.card (classAut Γ K c.out) : ℚ)⁻¹ • f c.out :=
        finsum_eq_sum_of_fintype _
    _ ≤ ∑ _c : DoubleCosets Γ K, (1 : ℚ) • C := by grw [hf, Nat.cast_inv_le_one]
    _ = _ := by simp

/-- If `√(f g) ≤ M` for every `g`, the class sum of the real function `f` is at most the number of
double cosets `Γ \ G / K` times `M ^ 2`. -/
lemma classSum_le_card_mul_sq {f : G → ℝ} {M : ℝ} (h_sqrt : ∀ g : G, √(f g) ≤ M) :
    classSum Γ K f ≤ Nat.card (DoubleCosets Γ K) * M ^ 2 :=
  classSum_le_card_mul (sq_nonneg M) fun g ↦ (Real.sqrt_le_iff.1 (h_sqrt g)).2

end New

end
