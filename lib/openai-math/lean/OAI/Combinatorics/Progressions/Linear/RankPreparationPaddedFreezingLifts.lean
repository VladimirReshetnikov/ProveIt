import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

@[simp] theorem pad_polynomial [DecidableEq J] (hmq : m ≤ q) :
    (L.pad q).polynomial = L.polynomial := by
  apply L.pad_sum hmq (fun layer => map (coordinateCopySum layer.label) layer.poly)
  change map (coordinateCopySum (R := ℝ) (PEmpty.elim : PEmpty → J))
    (0 : VectorPolynomial X ℝ (PEmpty → ℝ)) = 0
  exact map_zero _

theorem pad_identity [Fintype J] [DecidableEq J] (hmq : m ≤ q)
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E) :
    P = (L.pad q).polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E := by
  simpa only [L.pad_polynomial hmq] using hP

noncomputable def padCoordInclusion (hmq : m ≤ q) :
    (Σ j, (L j).Coord) → Σ j, (L.pad q j).Coord := fun a =>
  ⟨a.1.castLE hmq, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_castLE hmq a.1).symm) a.2⟩

private theorem padCoord_isLt (a : Σ j, (L.pad q j).Coord) : a.1.val < m := by
  rcases a with ⟨j, i⟩
  by_cases hj : j.val < m
  · exact hj
  · exact PEmpty.elim (cast (congrArg RankPreparationLayer.Coord
      (L.pad_apply_ge j (by omega))) i)

noncomputable def padCoordRestriction (a : Σ j, (L.pad q j).Coord) :
    Σ j, (L j).Coord :=
  ⟨⟨a.1.val, L.padCoord_isLt a⟩, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_lt a.1 (L.padCoord_isLt a))) a.2⟩

@[simp] theorem padCoordRestriction_inclusion (hmq : m ≤ q)
    (a : Σ j, (L j).Coord) :
    L.padCoordRestriction (L.padCoordInclusion hmq a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

@[simp] theorem padCoordInclusion_restriction (hmq : m ≤ q)
    (a : Σ j, (L.pad q j).Coord) :
    L.padCoordInclusion hmq (L.padCoordRestriction a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

noncomputable def padCoordEquiv (hmq : m ≤ q) :
    (Σ j, (L.pad q j).Coord) ≃ Σ j, (L j).Coord where
  toFun := L.padCoordRestriction
  invFun := L.padCoordInclusion hmq
  left_inv := L.padCoordInclusion_restriction hmq
  right_inv := L.padCoordRestriction_inclusion hmq

private theorem label_cast {A B : RankPreparationLayer X J} (h : A = B)
    (i : A.Coord) : B.label (cast (congrArg RankPreparationLayer.Coord h) i) = A.label i := by
  cases h
  rfl

private theorem eval_cast {A B : RankPreparationLayer X J} (h : A = B)
    (x : X → ℝ) (i : A.Coord) :
    eval x B.poly (cast (congrArg RankPreparationLayer.Coord h) i) = eval x A.poly i := by
  cases h
  rfl

private theorem coefficients_cast {A B : RankPreparationLayer X J} (h : A = B)
    (α : X →₀ ℕ) (i : A.Coord) :
    coefficients B.poly α (cast (congrArg RankPreparationLayer.Coord h) i) =
      coefficients A.poly α i := by
  cases h
  rfl

@[simp] theorem padCoordInclusion_label (hmq : m ≤ q) (a : Σ j, (L j).Coord) :
    (L.pad q (L.padCoordInclusion hmq a).1).label (L.padCoordInclusion hmq a).2 =
      (L a.1).label a.2 :=
  label_cast (L.pad_apply_castLE hmq a.1).symm a.2

@[simp] theorem padCoordEquiv_index (hmq : m ≤ q) (a : Σ j, (L.pad q j).Coord) :
    ((L.padCoordEquiv hmq a).1 : ℕ) = a.1.val := rfl

@[simp] theorem padCoordEquiv_label (hmq : m ≤ q) (a : Σ j, (L.pad q j).Coord) :
    (L (L.padCoordEquiv hmq a).1).label (L.padCoordEquiv hmq a).2 =
      (L.pad q a.1).label a.2 := by
  have h := L.padCoordInclusion_label hmq (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

@[simp] theorem padCoordInclusion_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L j).Coord) :
    eval x (L.pad q (L.padCoordInclusion hmq a).1).poly (L.padCoordInclusion hmq a).2 =
      eval x (L a.1).poly a.2 :=
  eval_cast (L.pad_apply_castLE hmq a.1).symm x a.2

@[simp] theorem padCoordEquiv_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L.pad q j).Coord) :
    eval x (L (L.padCoordEquiv hmq a).1).poly (L.padCoordEquiv hmq a).2 =
      eval x (L.pad q a.1).poly a.2 := by
  have h := L.padCoordInclusion_eval hmq x (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

@[simp] theorem padCoordInclusion_coefficients (hmq : m ≤ q) (α : X →₀ ℕ)
    (a : Σ j, (L j).Coord) :
    coefficients (L.pad q (L.padCoordInclusion hmq a).1).poly α
        (L.padCoordInclusion hmq a).2 = coefficients (L a.1).poly α a.2 :=
  coefficients_cast (L.pad_apply_castLE hmq a.1).symm α a.2

@[simp] theorem padCoordEquiv_coefficients (hmq : m ≤ q) (α : X →₀ ℕ)
    (a : Σ j, (L.pad q j).Coord) :
    coefficients (L (L.padCoordEquiv hmq a).1).poly α (L.padCoordEquiv hmq a).2 =
      coefficients (L.pad q a.1).poly α a.2 := by
  have h := L.padCoordInclusion_coefficients hmq α (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

theorem pad_coordinateCopySum {R : Type*} [CommRing R] [DecidableEq J]
    (hmq : m ≤ q) (v : (Σ j, (L j).Coord) → R) :
    coordinateCopySum (fun a : Σ j, (L.pad q j).Coord => (L.pad q a.1).label a.2)
        (fun a => v (L.padCoordEquiv hmq a)) =
      coordinateCopySum (fun a : Σ j, (L j).Coord => (L a.1).label a.2) v := by
  ext j
  apply Fintype.sum_equiv (L.padCoordEquiv hmq)
  intro a
  dsimp only
  simp only [L.padCoordEquiv_label]

theorem pad_coordinateCopySum_family {R : Type*} [CommRing R] [DecidableEq J]
    (hmq : m ≤ q) (v : ∀ j, (L j).Coord → R) :
    (∑ j, coordinateCopySum (L.pad q j).label
      (fun i => v (L.padCoordEquiv hmq ⟨j, i⟩).1 (L.padCoordEquiv hmq ⟨j, i⟩).2)) =
      ∑ j, coordinateCopySum (L j).label (v j) := by
  ext j
  simpa only [coordinateCopySum_apply, Fintype.sum_sigma, Finset.sum_apply] using
    congrFun (L.pad_coordinateCopySum hmq (fun a => v a.1 a.2)) j

theorem pad_integerRemainder [Fintype J] [DecidableEq J] (hmq : m ≤ q)
    (ip : J → MvPolynomial X ℤ) (β : ∀ j, (L j).Coord → MvPolynomial X ℤ) :
    (L.pad q).integerRemainder ip
      (fun j i => β (L.padCoordEquiv hmq ⟨j, i⟩).1 (L.padCoordEquiv hmq ⟨j, i⟩).2) =
        L.integerRemainder ip β := by
  unfold integerRemainder
  rw [L.pad_coordinateCopySum_family hmq β]

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

noncomputable def unpadCenter (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) : ∀ j, (L j).Coord → ℝ := fun j i =>
  c ((L.padCoordEquiv hmq).symm ⟨j, i⟩).1 ((L.padCoordEquiv hmq).symm ⟨j, i⟩).2

@[simp] theorem unpadCenter_equiv (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (a : Σ j, (L.pad q j).Coord) :
    L.unpadCenter hmq c (L.padCoordEquiv hmq a).1 (L.padCoordEquiv hmq a).2 =
      c a.1 a.2 := by
  exact congrArg (fun b : Σ j, (L.pad q j).Coord => c b.1 b.2)
    ((L.padCoordEquiv hmq).symm_apply_apply a)

private theorem space_cast {K L' : RankPreparationLayer X J} (h : K = L')
    (v : K.Coord → ℝ) (hv : v ∈ K.space) :
    (fun i => v (cast (congrArg RankPreparationLayer.Coord h.symm) i)) ∈ L'.space := by
  subst L'
  exact hv

theorem unpadCenter_mem (hmq : m ≤ q) (c : ∀ j, (L.pad q j).Coord → ℝ)
    (hc : ∀ j, c j ∈ (L.pad q j).space) (j : Fin m) :
    L.unpadCenter hmq c j ∈ (L j).space := by
  exact space_cast (L.pad_apply_castLE hmq j) (c (j.castLE hmq)) (hc (j.castLE hmq))

noncomputable def padFullTaggedEquiv (hmq : m ≤ q) :
    (X ⊕ (Σ j, (L.pad q j).Coord)) ≃ (X ⊕ (Σ j, (L j).Coord)) :=
  (Equiv.refl X).sumCongr (L.padCoordEquiv hmq)

@[simp] theorem padFullTaggedEquiv_weight (hmq : m ≤ q)
    (a : X ⊕ (Σ j, (L.pad q j).Coord)) :
    fullTaggedVariableWeight (fun j => (L j).Coord) (L.padFullTaggedEquiv hmq a) =
      fullTaggedVariableWeight (fun j => (L.pad q j).Coord) a := by
  cases a with
  | inl x => rfl
  | inr a =>
    change (L.padCoordEquiv hmq a).1.val + 1 = a.1.val + 1
    rw [L.padCoordEquiv_index]

theorem pad_fullTaggedPhysicalIntegerPoint (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (x : X → ℤ)
    (a : X ⊕ (Σ j, (L.pad q j).Coord)) :
    fullTaggedPhysicalIntegerPoint (fun j => (L.pad q j).Coord)
        (fun j => (L.pad q j).poly) c x a =
      fullTaggedPhysicalIntegerPoint (fun j => (L j).Coord)
        (fun j => (L j).poly) (L.unpadCenter hmq c) x (L.padFullTaggedEquiv hmq a) := by
  cases a with
  | inl x => rfl
  | inr a =>
    change round (eval (fun i => (x i : ℝ)) (L.pad q a.1).poly a.2 - c a.1 a.2) =
      round (eval (fun i => (x i : ℝ)) (L (L.padCoordEquiv hmq a).1).poly
        (L.padCoordEquiv hmq a).2 -
        L.unpadCenter hmq c (L.padCoordEquiv hmq a).1 (L.padCoordEquiv hmq a).2)
    rw [L.padCoordEquiv_eval, L.unpadCenter_equiv]

theorem pad_fullTaggedPhysicalIntegerPoint_restrict (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (x : X → ℤ) :
    (fun a => fullTaggedPhysicalIntegerPoint (fun j => (L.pad q j).Coord)
      (fun j => (L.pad q j).poly) c x ((L.padFullTaggedEquiv hmq).symm a)) =
    fullTaggedPhysicalIntegerPoint (fun j => (L j).Coord)
      (fun j => (L j).poly) (L.unpadCenter hmq c) x := by
  funext a
  rw [L.pad_fullTaggedPhysicalIntegerPoint, Equiv.apply_symm_apply]

theorem pad_fullTagged_observer {E : Type*} (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (x : X → ℤ)
    (F : ((X ⊕ (Σ j, (L j).Coord)) → ℤ) → E) :
    F (fun a => fullTaggedPhysicalIntegerPoint (fun j => (L.pad q j).Coord)
      (fun j => (L.pad q j).poly) c x ((L.padFullTaggedEquiv hmq).symm a)) =
    F (fullTaggedPhysicalIntegerPoint (fun j => (L j).Coord)
      (fun j => (L j).poly) (L.unpadCenter hmq c) x) := by
  rw [L.pad_fullTaggedPhysicalIntegerPoint_restrict]

noncomputable def padLowTaggedEquiv (hmq : m ≤ q) (d : ℕ) :
    LowTaggedIndex (fun j => (L.pad q j).Coord) d ≃
      LowTaggedIndex (fun j => (L j).Coord) d :=
  (L.padCoordEquiv hmq).subtypeEquiv (fun a => by
    change a.1.val + 1 ≤ d ↔ (L.padCoordEquiv hmq a).1.val + 1 ≤ d
    rw [L.padCoordEquiv_index])

theorem pad_lowTagged_card (hmq : m ≤ q) (d : ℕ) :
    Fintype.card (LowTaggedIndex (fun j => (L.pad q j).Coord) d) =
      Fintype.card (LowTaggedIndex (fun j => (L j).Coord) d) :=
  Fintype.card_congr (L.padLowTaggedEquiv hmq d)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {X J : Type} {Vars : Type*} {m q : ℕ}
    (L : RankPreparationFamily X J m)

noncomputable def unpadFreezingLifts (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ) :
    ∀ j, (L j).Coord → MvPolynomial Vars ℤ := fun j i =>
  β (L.padCoordInclusion hmq ⟨j, i⟩).1 (L.padCoordInclusion hmq ⟨j, i⟩).2

theorem unpadFreezingLifts_degree (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ)
    (hβ : ∀ j i, (β j i).totalDegree ≤ j.val + 1) :
    ∀ j i, (L.unpadFreezingLifts hmq β j i).totalDegree ≤ j.val + 1 := by
  intro j i
  exact hβ (L.padCoordInclusion hmq ⟨j, i⟩).1 (L.padCoordInclusion hmq ⟨j, i⟩).2

theorem unpadFreezingLifts_bound (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ)
    (c : ∀ j, (L.pad q j).Coord → ℝ)
    (point : (Vars → ℝ) → X → ℝ) (domain : Set (Vars → ℝ)) (ε : Fin q → ℝ)
    (hsmall : ∀ t ∈ domain, ∀ j i,
      |eval (point t) (L.pad q j).poly i - c j i -
        MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤ ε j) :
    ∀ t ∈ domain, ∀ j i,
      |eval (point t) (L j).poly i - L.unpadCenter hmq c j i -
        MvPolynomial.eval t
          (MvPolynomial.map (Int.castRingHom ℝ) (L.unpadFreezingLifts hmq β j i))| ≤
        ε (j.castLE hmq) := by
  intro t ht j i
  have h := hsmall t ht (L.padCoordInclusion hmq ⟨j, i⟩).1
    (L.padCoordInclusion hmq ⟨j, i⟩).2
  rw [L.padCoordInclusion_eval hmq (point t)] at h
  exact h

theorem exists_unpadded_freezing_lifts (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ)
    (hβ : ∀ j i, (β j i).totalDegree ≤ j.val + 1)
    (c : ∀ j, (L.pad q j).Coord → ℝ)
    (point : (Vars → ℝ) → X → ℝ) (domain : Set (Vars → ℝ)) (ε : Fin q → ℝ)
    (hsmall : ∀ t ∈ domain, ∀ j i,
      |eval (point t) (L.pad q j).poly i - c j i -
        MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤ ε j) :
    ∃ βold : ∀ j, (L j).Coord → MvPolynomial Vars ℤ,
      (∀ j i, (βold j i).totalDegree ≤ j.val + 1) ∧
      ∀ t ∈ domain, ∀ j i,
        |eval (point t) (L j).poly i - L.unpadCenter hmq c j i -
          MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (βold j i))| ≤
          ε (j.castLE hmq) :=
  ⟨L.unpadFreezingLifts hmq β, L.unpadFreezingLifts_degree hmq β hβ,
    L.unpadFreezingLifts_bound hmq β c point domain ε hsmall⟩

theorem pad_coordinateWeighted_sum (hmq : m ≤ q) (ε : Fin q → ℝ) :
    (∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * ε (j.castLE hmq)) =
      ∑ j : Fin q, (Fintype.card (L.pad q j).Coord : ℝ) * ε j := by
  apply Fintype.sum_of_injective (Fin.castLE hmq)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin q => k.val) hij))
  · intro j hj
    have hge : m ≤ j.val := by
      by_contra hnot
      have hlt : j.val < m := by omega
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    rw [L.pad_apply_ge j hge]
    change (Fintype.card PEmpty : ℝ) * ε j = 0
    simp
  · intro j
    rw [L.pad_apply_castLE hmq j]

end Erdos3.RankPreparationFamily

end

end OAI
