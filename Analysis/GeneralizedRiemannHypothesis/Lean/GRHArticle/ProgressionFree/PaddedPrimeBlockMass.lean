import GRHArticle.ProgressionFree.LightPrimeBlocks

/-!
# Padding exponent coordinates of weight zero

Unused slots in a prime block have zero reciprocal weight. Only vectors
that have exponent zero in every unused slot contribute to the mass.
Restricting and padding such vectors transports both the reciprocal
mass and the affine-progression condition.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- Extend a vector by zero off the embedded coordinates. -/
noncomputable def zeroPadExponentVector {ι κ A : Type*} [Zero A]
    (e : ι ↪ κ) (v : ι → A) (q : κ) : A :=
  if h : q ∈ Set.range e then v h.choose else 0

theorem zeroPadExponentVector_apply {ι κ A : Type*} [Zero A]
    (e : ι ↪ κ) (v : ι → A) (p : ι) : zeroPadExponentVector e v (e p) = v p := by
  have h : e p ∈ Set.range e := Set.mem_range_self p
  rw [zeroPadExponentVector,dif_pos h]
  exact congrArg v (e.injective h.choose_spec)

theorem zeroPadExponentVector_apply_of_notMem {ι κ A : Type*} [Zero A]
    (e : ι ↪ κ) (v : ι → A) {q : κ} (hq : q ∉ Set.range e) :
    zeroPadExponentVector e v q = 0 :=
  dif_neg hq

theorem zeroPadExponentVector_restrict {ι κ A : Type*} [Zero A]
    (e : ι ↪ κ) (v : κ → A) (hv : ∀ q ∉ Set.range e, v q = 0) :
    zeroPadExponentVector e (fun p ↦ v (e p)) = v := by
  funext q
  by_cases hq : q ∈ Set.range e
  · obtain ⟨p,rfl⟩ := hq
    exact zeroPadExponentVector_apply e _ p
  · rw [zeroPadExponentVector_apply_of_notMem e _ hq,hv q hq]

/-- The zero slice of a rule on more exponent coordinates. -/
def paddedRuleSlice {ι κ : Type*} (e : ι ↪ κ) (F : Set (κ → ℕ)) : Set (ι → ℕ) :=
  {v | zeroPadExponentVector e v ∈ F}

/-- Insert unused exponent coordinates that are required to be zero. -/
def paddedExponentRule {ι κ : Type*} (e : ι ↪ κ) (F : Set (ι → ℕ)) : Set (κ → ℕ) :=
  {v | (∀ q ∉ Set.range e, v q = 0) ∧ (fun p ↦ v (e p)) ∈ F}

theorem paddedRuleSlice_paddedExponentRule {ι κ : Type*} (e : ι ↪ κ) (F : Set (ι → ℕ)) :
    paddedRuleSlice e (paddedExponentRule e F) = F := by
  ext v
  have he : (fun p ↦ zeroPadExponentVector e v (e p)) = v :=
    funext (zeroPadExponentVector_apply e v)
  exact ⟨fun h ↦ he ▸ h.2, fun h ↦
    ⟨fun _ hq ↦ zeroPadExponentVector_apply_of_notMem e v hq,he.symm ▸ h⟩⟩

theorem paddedRuleSlice_greedyExponentPatterns {ι κ : Type*} {k : ℕ} (hk : 2 ≤ k) (e : ι ↪ κ) :
    paddedRuleSlice e (greedyExponentPatterns κ k) = greedyExponentPatterns ι k := by
  ext v
  constructor
  · intro h p
    exact (zeroPadExponentVector_apply e v p) ▸ h (e p)
  · intro h q
    by_cases hq : q ∈ Set.range e
    · obtain ⟨p,rfl⟩ := hq
      exact (zeroPadExponentVector_apply e v p).symm ▸ h p
    · rw [zeroPadExponentVector_apply_of_notMem e v hq]
      exact mem_greedyLengthExponents_of_lt hk (by omega)

theorem kTermVectorAPFree_paddedRuleSlice {ι κ : Type*} {k : ℕ}
    (e : ι ↪ κ) {F : Set (κ → ℕ)} (hF : KTermVectorAPFree k F) :
    KTermVectorAPFree k (paddedRuleSlice e F) := by
  intro x a d hm hx p
  have ha (i : Fin k) (q : κ) : ((zeroPadExponentVector e (x i) q : ℕ) : ℤ) =
      zeroPadExponentVector e a q + (i.val : ℤ)*zeroPadExponentVector e d q := by
    by_cases hq : q ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hq
      simpa only [zeroPadExponentVector_apply] using hx i j
    · simp only [zeroPadExponentVector_apply_of_notMem _ _ hq,Nat.cast_zero,mul_zero,add_zero]
  have h := hF (fun i ↦ zeroPadExponentVector e (x i))
    (zeroPadExponentVector e a) (zeroPadExponentVector e d) hm ha (e p)
  simpa only [zeroPadExponentVector_apply] using h

theorem kTermVectorAPFree_paddedExponentRule {ι κ : Type*} {k : ℕ} (hk : 2 ≤ k)
    (e : ι ↪ κ) {F : Set (ι → ℕ)} (hF : KTermVectorAPFree k F) :
    KTermVectorAPFree k (paddedExponentRule e F) := by
  intro x a d hm hx q
  by_cases hq : q ∈ Set.range e
  · obtain ⟨p,rfl⟩ := hq
    exact hF (fun i p ↦ x i (e p)) (fun p ↦ a (e p)) (fun p ↦ d (e p))
      (fun i ↦ (hm i).2) (fun i p ↦ hx i (e p)) p
  · let i₀ : Fin k := ⟨0,by omega⟩
    let i₁ : Fin k := ⟨1,by omega⟩
    have h₀ := hx i₀ q
    have h₁ := hx i₁ q
    rw [(hm i₀).1 q hq] at h₀
    rw [(hm i₁).1 q hq] at h₁
    simp [i₀] at h₀
    simp [i₁] at h₁
    omega

private theorem reciprocalExponentWeight_pad {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (u : κ → ℝ) (v : ι → ℕ) :
    reciprocalExponentWeight u (zeroPadExponentVector e v) =
      reciprocalExponentWeight (fun p ↦ u (e p)) v := by
  unfold reciprocalExponentWeight
  calc
    _ = ∏ q ∈ (univ : Finset ι).map e, u q ^ zeroPadExponentVector e v q := by
      symm
      refine prod_subset (subset_univ _) (fun q _ hq ↦ ?_)
      have h : q ∉ Set.range e := by
        rintro ⟨p,rfl⟩
        exact hq (mem_map.mpr ⟨p,mem_univ _,rfl⟩)
      rw [zeroPadExponentVector_apply_of_notMem e v h,pow_zero]
    _ = _ := by rw [prod_map]; simp only [zeroPadExponentVector_apply]

/-- Weight zero on the missing coordinates makes the mass equal to the
mass of the zero slice on the retained coordinates. -/
theorem reciprocalExponentMass_eq_paddedRuleSlice {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (u : κ → ℝ) (hu : ∀ q ∉ Set.range e, u q = 0)
    (F : Set (κ → ℕ)) :
    reciprocalExponentMass u F =
      reciprocalExponentMass (fun p ↦ u (e p)) (paddedRuleSlice e F) := by
  let V : Set (κ → ℕ) := {v | v ∈ F ∧ ∀ q ∉ Set.range e, v q = 0}
  let W := paddedRuleSlice e F
  have hMass : reciprocalExponentMass u F = reciprocalExponentMass u V := by
    apply tsum_congr
    intro v
    by_cases hF : v ∈ F
    · by_cases hv : ∀ q ∉ Set.range e, v q = 0
      · simp only [Set.indicator_of_mem hF,Set.indicator_of_mem (show v ∈ V from ⟨hF,hv⟩)]
      · have hV : v ∉ V := fun h ↦ hv h.2
        rw [Set.indicator_of_mem hF,Set.indicator_of_notMem hV]
        push Not at hv
        obtain ⟨q,hq,hn⟩ := hv
        unfold reciprocalExponentWeight
        exact prod_eq_zero (mem_univ q) (by rw [hu q hq,zero_pow hn])
    · have hV : v ∉ V := fun h ↦ hF h.1
      rw [Set.indicator_of_notMem hF,Set.indicator_of_notMem hV]
  let E : W ≃ V :=
    { toFun := fun v ↦ ⟨zeroPadExponentVector e v.val, v.property,
        fun _ h ↦ zeroPadExponentVector_apply_of_notMem e v.val h⟩
      invFun := fun v ↦ ⟨fun p ↦ v.val (e p), by
        change zeroPadExponentVector e (fun p ↦ v.val (e p)) ∈ F
        rw [zeroPadExponentVector_restrict e v.val v.property.2]
        exact v.property.1⟩
      left_inv := fun v ↦ Subtype.ext (funext (zeroPadExponentVector_apply e v.val))
      right_inv := fun v ↦ Subtype.ext (zeroPadExponentVector_restrict e v.val v.property.2) }
  rw [hMass,reciprocalExponentMass_eq_tsum_subtype,reciprocalExponentMass_eq_tsum_subtype,← E.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  exact reciprocalExponentWeight_pad e u v.val

end GRHArticle.ProgressionFree
