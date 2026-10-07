/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientProjection (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    (L ⧸ I) →ₗ⁅ℚ⁆ (M ⧸ J) :=
  lieQuotientDescend I ((lieQuotientMap J).comp φ)
    (fun x hx => (lieQuotientMap_eq_zero J (φ x)).mpr (hφ x hx))

@[simp] theorem lieQuotientProjection_mk (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) (x : L) :
    lieQuotientProjection I J φ hφ (lieQuotientMap I x) = lieQuotientMap J (φ x) := rfl

noncomputable def lieQuotientFiberProduct (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    LieSubalgebra ℚ ((L ⧸ I) × M) where
  carrier := {z | lieQuotientProjection I J φ hφ z.1 = lieQuotientMap J z.2}
  zero_mem' := by simp
  add_mem' hx hy := by
    change _ = _
    simpa only [Prod.fst_add, Prod.snd_add, map_add] using congrArg₂ (· + ·) hx hy
  smul_mem' c x hx := by
    change lieQuotientProjection I J φ hφ (c • x.1) = lieQuotientMap J (c • x.2)
    simpa only [map_smul] using congrArg (c • ·) hx
  lie_mem' := by
    intro x y hx hy
    change lieQuotientProjection I J φ hφ ⁅x.1, y.1⁆ = lieQuotientMap J ⁅x.2, y.2⁆
    simpa only [LieHom.map_lie] using congrArg₂ (⁅·, ·⁆) hx hy

noncomputable def lieQuotientFiberMap (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    L →ₗ⁅ℚ⁆ lieQuotientFiberProduct I J φ hφ where
  toFun x := ⟨(lieQuotientMap I x, φ x), rfl⟩
  map_add' x y := by apply Subtype.ext; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c x := by apply Subtype.ext; exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  map_lie' {x y} := by
    apply Subtype.ext
    exact Prod.ext (LieHom.map_lie _ _ _) (LieHom.map_lie _ _ _)

theorem lieQuotientFiberMap_bijective (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) :
    Function.Bijective (lieQuotientFiberMap I J φ hφ) := by
  constructor
  · intro x y hxy
    have hq : lieQuotientMap I (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun z : lieQuotientFiberProduct I J φ hφ => z.val.1) hxy
    have hp : φ (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun z : lieQuotientFiberProduct I J φ hφ => z.val.2) hxy
    exact sub_eq_zero.mp (hinj (x - y) ((lieQuotientMap_eq_zero I _).mp hq) hp)
  · intro z
    obtain ⟨x, hx⟩ := lieQuotientMap_surjective I z.val.1
    have hc : lieQuotientMap J (z.val.2 - φ x) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact z.property.symm.trans (congrArg (lieQuotientProjection I J φ hφ) hx.symm)
    obtain ⟨a, ha, hpa⟩ := honto (z.val.2 - φ x) ((lieQuotientMap_eq_zero J _).mp hc)
    refine ⟨x + a, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change lieQuotientMap I (x + a) = z.val.1
      rw [map_add, (lieQuotientMap_eq_zero I a).mpr ha, add_zero, hx]
    · change φ (x + a) = z.val.2
      rw [map_add, hpa]
      abel

noncomputable def lieQuotientFiberEquiv (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) :
    L ≃ₗ⁅ℚ⁆ lieQuotientFiberProduct I J φ hφ :=
  LieEquiv.ofBijective (lieQuotientFiberMap I J φ hφ)
    (lieQuotientFiberMap_bijective I J φ hφ hinj honto)

@[simp] theorem lieQuotientFiberEquiv_apply (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) (x : L) :
    (lieQuotientFiberEquiv I J φ hφ hinj honto x).val =
      (lieQuotientMap I x, φ x) := rfl

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include hφ in

theorem mem_layer_iff_quotient_and_projection
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0) (j : ℕ) (x : L) :
    x ∈ F.layer j ↔
      lieQuotientMap (F.layerIdeal s) x ∈
        (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap ∧ φ x ∈ G.layer j := by
  constructor
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hφ j x hx⟩
  · rintro ⟨⟨a, ha, hqa⟩, hp⟩
    have htop : x - a ∈ F.layer s := by
      apply (lieQuotientMap_eq_zero (F.layerIdeal s) _).mp
      rw [map_sub, sub_eq_zero]
      exact hqa.symm
    by_cases hjs : j ≤ s
    · have hd := F.antitone hjs htop
      have := (F.layer j).add_mem hd ha
      simpa only [sub_add_cancel] using this
    · have hj : s + 1 ≤ j := by omega
      have hz : φ x = 0 := by
        have h := G.antitone hj hp
        rw [G.terminal] at h
        exact h
      have ha0 : a = 0 := by
        have h := F.antitone hj ha
        rw [F.terminal] at h
        exact h
      rw [ha0, sub_zero] at htop
      rw [hinj x htop hz]
      exact (F.layer j).zero_mem

noncomputable def quotientFiberEquiv
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0)
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y) :
    L ≃ₗ⁅ℚ⁆ lieQuotientFiberProduct (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) :=
  lieQuotientFiberEquiv (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) hinj honto

theorem quotientFiberEquiv_layer_surjective
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0)
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (j : ℕ) (z : lieQuotientFiberProduct (F.layerIdeal s) (G.layerIdeal s) φ (hφ s))
    (hq : z.val.1 ∈ (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hp : z.val.2 ∈ G.layer j) :
    ∃ x ∈ F.layer j, F.quotientFiberEquiv G φ hφ hinj honto x = z := by
  obtain ⟨x, hx⟩ := (F.quotientFiberEquiv G φ hφ hinj honto).surjective z
  refine ⟨x, (F.mem_layer_iff_quotient_and_projection G φ hφ hinj j x).mpr ?_, hx⟩
  have he : (lieQuotientMap (F.layerIdeal s) x, φ x) = z.val :=
    congrArg Subtype.val hx
  have hqe : lieQuotientMap (F.layerIdeal s) x = z.val.1 := congrArg Prod.fst he
  have hpe : φ x = z.val.2 := congrArg Prod.snd he
  rw [← hqe] at hq
  rw [← hpe] at hp
  exact ⟨hq, hp⟩

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_quotient_marked_layer_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (j : ℕ) (a : L ⧸ F.layerIdeal s) (b : M)
    (ha : a ∈ (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hb : b ∈ G.layer j)
    (hcompat : lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) a =
      lieQuotientMap (G.layerIdeal s) b) :
    ∃ x ∈ F.layer j, lieQuotientMap (F.layerIdeal s) x = a ∧ φ x = b := by
  by_cases hjs : j ≤ s
  · obtain ⟨z, hz, hza⟩ := ha
    have hδ : b - φ z ∈ G.layer s := by
      apply (lieQuotientMap_eq_zero (G.layerIdeal s) _).mp
      rw [map_sub, sub_eq_zero]
      exact hcompat.symm.trans
        (congrArg (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)) hza.symm)
    obtain ⟨t, ht, hφt⟩ := honto (b - φ z) hδ
    refine ⟨z + t, (F.layer j).add_mem hz (F.antitone hjs ht), ?_, ?_⟩
    · rw [map_add, (lieQuotientMap_eq_zero (F.layerIdeal s) t).mpr ht, add_zero]
      exact hza
    · rw [map_add, hφt]
      abel
  · have hj : s + 1 ≤ j := by omega
    have ha0 : a = 0 := by
      obtain ⟨z, hz, rfl⟩ := ha
      have hz0 : z = 0 := by
        have h := F.antitone hj hz
        rw [F.terminal] at h
        exact h
      rw [hz0, map_zero]
    have hb0 : b = 0 := by
      have h := G.antitone hj hb
      rw [G.terminal] at h
      exact h
    exact ⟨0, (F.layer j).zero_mem, by rw [map_zero, ha0], by rw [map_zero, hb0]⟩

theorem quotientFiberMap_layer_surjective
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (j : ℕ) (z : lieQuotientFiberProduct (F.layerIdeal s) (G.layerIdeal s) φ (hφ s))
    (hq : z.val.1 ∈ (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hp : z.val.2 ∈ G.layer j) :
    ∃ x ∈ F.layer j,
      lieQuotientFiberMap (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) x = z := by
  obtain ⟨x, hx, hqx, hφx⟩ :=
    F.exists_quotient_marked_layer_lift G φ hφ honto j z.val.1 z.val.2 hq hp z.property
  exact ⟨x, hx, Subtype.ext (Prod.ext hqx hφx)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_adapted_quotient_fiber_polynomial_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (w : σ → ℕ) (pbar : VectorPolynomial σ ℚ (L ⧸ F.layerIdeal s))
    (q : VectorPolynomial σ ℚ M)
    (hcompat : map (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)).toLinearMap
      pbar = map (lieQuotientMap (G.layerIdeal s)).toLinearMap q)
    (hpbar : ∀ a, coefficients pbar a ∈
      (F.layer (Finsupp.weight w a)).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hq : G.Adapted w q) :
    ∃ p : VectorPolynomial σ ℚ L,
      F.Adapted w p ∧ map (lieQuotientMap (F.layerIdeal s)).toLinearMap p = pbar ∧
        map φ.toLinearMap p = q := by
  classical
  have hc (a : σ →₀ ℕ) :
      lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) (coefficients pbar a) =
        lieQuotientMap (G.layerIdeal s) (coefficients q a) := by
    simpa only [coefficients_map, LieHom.coe_toLinearMap] using
      congrArg (fun P => coefficients P a) hcompat
  have hex (a : σ →₀ ℕ) : ∃ x ∈ F.layer (Finsupp.weight w a),
      lieQuotientMap (F.layerIdeal s) x = coefficients pbar a ∧ φ x = coefficients q a :=
    F.exists_quotient_marked_layer_lift G φ hφ honto (Finsupp.weight w a)
      (coefficients pbar a) (coefficients q a) (hpbar a)
      ((G.adapted_iff_coefficients w q).mp hq a) (hc a)
  let v (a : σ →₀ ℕ) : L :=
    if coefficients pbar a = 0 ∧ coefficients q a = 0 then 0 else Classical.choose (hex a)
  have hv (a : σ →₀ ℕ) : v a ∈ F.layer (Finsupp.weight w a) ∧
      lieQuotientMap (F.layerIdeal s) (v a) = coefficients pbar a ∧
        φ (v a) = coefficients q a := by
    dsimp only [v]
    split_ifs with hz
    · exact ⟨(F.layer _).zero_mem, (map_zero _).trans hz.1.symm,
        (map_zero _).trans hz.2.symm⟩
    · exact Classical.choose_spec (hex a)
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset
    ((coefficients pbar).support ∪ (coefficients q).support) v (by
      intro a ha
      apply Finset.mem_union.mpr
      by_cases hp0 : coefficients pbar a = 0
      · right
        apply Finsupp.mem_support_iff.mpr
        intro hq0
        exact ha (by simp only [v, hp0, hq0, and_self, ite_true])
      · exact Or.inl (Finsupp.mem_support_iff.mpr hp0))
  let p : VectorPolynomial σ ℚ L := coefficients.symm c
  have hcoef (a : σ →₀ ℕ) : coefficients p a = v a := by
    simp only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply]
  refine ⟨p, ?_, ?_, ?_⟩
  · apply (F.adapted_iff_coefficients w p).mpr
    intro a
    rw [hcoef]
    exact (hv a).1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.2

theorem exists_quotient_fiber_polynomialOrbit_lift
    {r : ℕ} (F : NilpotentLieFiltration L (r + 1)) (G : NilpotentLieFiltration M (r + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (honto : ∀ y ∈ G.layer (r + 1), ∃ x ∈ F.layer (r + 1), φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.PolynomialOrbit w) (q : G.PolynomialOrbit w)
    (hcompat : map (lieQuotientProjection (F.layerIdeal (r + 1)) (G.layerIdeal (r + 1))
      φ (hφ (r + 1))).toLinearMap pbar.log =
        map (lieQuotientMap (G.layerIdeal (r + 1))).toLinearMap q.log) :
    ∃ p : F.PolynomialOrbit w,
      map (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap p.log = pbar.log ∧
        map φ.toLinearMap p.log = q.log := by
  have hpbar : ∀ a, coefficients pbar.log a ∈
      (F.layer (Finsupp.weight w a)).map
        (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap :=
    (F.quotientTop.adapted_iff_coefficients w pbar.log).mp pbar.adapted
  obtain ⟨p, hp, heq, hproj⟩ := F.exists_adapted_quotient_fiber_polynomial_lift G φ hφ honto
    w pbar.log q.log hcompat hpbar q.adapted
  exact ⟨polynomialOrbitOfLog p hp, heq, hproj⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

def quotientInducedMapHeightBudget (p : ℝ) : ℝ :=
  let q := p + (p + 3) ^ 7 + 1
  ((q + 2) ^ 4 + q + 2) ^ 4

theorem exists_quotientInducedMapHeightBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → quotientInducedMapHeightBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + 3) ^ 7 + 1
  let P : Polynomial ℕ := ((Q + 2) ^ 4 + Q + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, quotientInducedMapHeightBudget, Polynomial.eval₂_pow] using hbound p hp

theorem lieQuotientProjection_basis_logHeight
    {L M ι κ β γ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]
    (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (c : Basis γ ℚ (M ⧸ J))
    (φ : L →ₗ⁅ℚ⁆ M) (hIJ : ∀ x ∈ I, φ x ∈ J)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hJ : ∀ i j, rationalLogHeight (c.repr (lieQuotientMap J (f i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (lieQuotientProjection I J φ hIJ (b i)) j) ≤
      quotientInducedMapHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hsection, hSH⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (S x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) : rationalLogHeight (e.repr (S (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hSH j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hseven]
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith only [hp]
  have hmarked (i : β) (j : κ) : rationalLogHeight (f.repr (φ (S (b i))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
      (fun a k => (hφ a k).trans hpq) (S (b i)) (fun a => (hS i a).trans hsevenq) j
  let t := (q + 2) ^ 4 + q
  have hfour : 0 ≤ (q + 2) ^ 4 := by positivity
  have ht : 0 ≤ t := add_nonneg hfour hq
  have hqt : q ≤ t := le_add_of_nonneg_left hfour
  have hpowt : (q + 2) ^ 4 ≤ t := le_add_of_nonneg_right hq
  intro i j
  have hinduced : lieQuotientProjection I J φ hIJ (b i) = lieQuotientMap J (φ (S (b i))) := by
    simpa only [hright] using lieQuotientProjection_mk I J φ hIJ (S (b i))
  rw [hinduced]
  exact linearMap_coordinate_logHeight f c (lieQuotientMap J).toLinearMap ht
    (hκ.trans (hpq.trans hqt)) (fun a k => (hJ a k).trans (hpq.trans hqt))
    (φ (S (b i))) (fun a => (hmarked i a).trans hpowt) j

end Erdos3

end

section

namespace Erdos3
open Module

noncomputable def quotientInducedMarkHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 3) ^ 7 + 3) ^ 4

theorem quotientInducedMark_basis_logHeight
    {L M ι κ β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype β]
    (I : LieIdeal ℚ L) (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (φ : L →ₗ⁅ℚ⁆ M)
    (hker : ∀ x ∈ I, φ x = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (f.repr (quotientInducedMark I φ hker (b i)) j) ≤
      quotientInducedMarkHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨sectionMap, hsection, hheight⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (sectionMap x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤
      Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith))
      (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) :
      rationalLogHeight (e.repr (sectionMap (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hheight j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith
  intro i j
  have hinduced : quotientInducedMark I φ hker (b i) = φ (sectionMap (b i)) := by
    simpa only [hright] using quotientInducedMark_mk I φ hker (sectionMap (b i))
  rw [hinduced]
  have hbound := linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
    (fun a k => (hφ a k).trans hpq) (sectionMap (b i))
    (fun a => (hS i a).trans hsevenq) j
  change rationalLogHeight (f.repr (φ (sectionMap (b i))) j) ≤ (q + 2) ^ 4 at hbound
  convert hbound using 1
  unfold quotientInducedMarkHeightBudget q
  congr 1
  ring

namespace RationalFilteredNilmanifold

theorem quotientInducedMark_native_logHeight
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d f n : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Fmark : RationalFilteredNilmanifold M t f)
    (I : LieIdeal ℚ L) (Q : RationalFilteredNilmanifold (L ⧸ I) r n)
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, φ x = 0)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight
      (Fmark.basis.repr (quotientInducedMark I φ hker (Q.basis j)) i) ≤
      quotientInducedMarkHeightBudget p := by
  intro i j
  exact quotientInducedMark_basis_logHeight I D.basis Fmark.basis Q.basis φ hker hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun a k => hprojection k a) (fun a k => hmark k a) j i

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1))

noncomputable def realificationTopQuotientHom :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  lieQuotientDescend (F.realification.layerIdeal (s + 1))
    (realLieHomToRat (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))))
    (fun x hx => (realification_mkQ_eq_zero_iff (F.layer (s + 1)) x).mpr hx)

@[simp] theorem realificationTopQuotientHom_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientHom (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

theorem realificationTopQuotientHom_bijective :
    Function.Bijective F.realificationTopQuotientHom := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
    obtain ⟨b, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (lieQuotientMap_eq_zero _ _).mpr
    apply (realification_mkQ_eq_zero_iff (F.layer (s + 1)) (a - b)).mp
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  · intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ
      (lieQuotientMap_surjective (F.layerIdeal (s + 1))) y
    exact ⟨lieQuotientMap (F.realification.layerIdeal (s + 1)) x, hx⟩

noncomputable def realificationTopQuotientEquiv :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) ≃ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  LieEquiv.ofBijective F.realificationTopQuotientHom F.realificationTopQuotientHom_bijective

@[simp] theorem realificationTopQuotientEquiv_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientEquiv (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

theorem realificationTopQuotientEquiv_mem_layer_iff (j : ℕ)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    F.realificationTopQuotientEquiv x ∈ F.quotientTop.realification.layer j ↔
      x ∈ F.realification.quotientTop.layer j := by
  change F.realificationTopQuotientEquiv x ∈
    ((F.layer j).map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap).baseChange ℝ ↔ _
  rw [realification_map]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, F.realificationTopQuotientEquiv.injective ?_⟩
    exact he
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem realificationTopQuotientEquiv_projection {M : Type*}
    [LieRing M] [LieAlgebra ℚ M] (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) x) =
      realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
        (F.realificationTopQuotientEquiv x) := by
  obtain ⟨v, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
  change realificationLieHom (lieQuotientMap (G.layerIdeal (s + 1)))
      (realificationLieHom φ v) =
    realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) v)
  induction v using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add v z hv hz => simp only [map_add, hv, hz]

end Erdos3.NilpotentLieFiltration

end

end OAI
