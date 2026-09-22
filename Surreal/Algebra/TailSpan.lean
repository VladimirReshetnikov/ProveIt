import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cofinite spans and multilinear detection

This file proves `tail:lem:stabilization` and `tail:lem:multilinear` in
`docs/surreal/tail-spans-and-differential-transcendence/article.tex`.

For an arbitrary family `v` in a finite-dimensional vector space, the cofinite
span `W` is the intersection of the spans left after every finite deletion. One
finite deletion already attains `W`; only finitely many indices have `v i ∉ W`;
and after removing those exceptions, every cofinite subfamily spans exactly `W`.
No finite alphabet, boundedness or countability hypothesis on the index set is
used.

A multilinear form that vanishes on all tuples of pairwise distinct family
members vanishes identically, provided every cofinite subfamily spans the
space. Spanning over the coefficient field transfers to every scalar extension
`K ⊗ W`, which is the form used in the source. The number of arguments may also
be zero.
-/

namespace Surreal.TailSpan

open Module Submodule

variable {M V I : Type*} [Field M] [AddCommGroup V] [Module M V]

/-- The span left after deleting a finite set of indices. -/
def deletedSpan (v : I → V) (F : Finset I) : Submodule M V :=
  span M (v '' (↑F : Set I)ᶜ)

/-- The cofinite span, or tail-span, of a family. -/
def cofiniteSpan (v : I → V) : Submodule M V :=
  ⨅ F : Finset I, deletedSpan (M := M) v F

theorem deletedSpan_anti (v : I → V) {F G : Finset I} (h : F ⊆ G) :
    deletedSpan (M := M) v G ≤ deletedSpan (M := M) v F :=
  span_mono (Set.image_mono (Set.compl_subset_compl.mpr (by exact_mod_cast h)))

theorem cofiniteSpan_le (v : I → V) (F : Finset I) :
    cofiniteSpan (M := M) v ≤ deletedSpan v F :=
  iInf_le _ F

variable [FiniteDimensional M V]

/-- `tail:lem:stabilization`: one finite deletion attains the cofinite span. -/
theorem exists_deletedSpan_eq_cofiniteSpan (v : I → V) :
    ∃ F₀ : Finset I, deletedSpan (M := M) v F₀ = cofiniteSpan v := by
  classical
  obtain ⟨F₀, -, hmin⟩ := (InvImage.wf (fun F : Finset I => finrank M (deletedSpan (M := M) v F))
    wellFounded_lt).has_min Set.univ ⟨∅, trivial⟩
  refine ⟨F₀, le_antisymm (le_iInf fun F => ?_) (cofiniteSpan_le v F₀)⟩
  have hle : deletedSpan (M := M) v (F ∪ F₀) ≤ deletedSpan v F₀ :=
    deletedSpan_anti v Finset.subset_union_right
  have heq : deletedSpan (M := M) v (F ∪ F₀) = deletedSpan v F₀ := by
    refine eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) ?_)
    exact not_lt.mp (hmin (F ∪ F₀) trivial)
  exact heq ▸ deletedSpan_anti v Finset.subset_union_left

/-- `tail:lem:stabilization`: only finitely many members lie outside the cofinite
span. -/
theorem finite_setOf_not_mem_cofiniteSpan (v : I → V) :
    {i | v i ∉ cofiniteSpan (M := M) v}.Finite := by
  obtain ⟨F₀, hF₀⟩ := exists_deletedSpan_eq_cofiniteSpan (M := M) v
  refine F₀.finite_toSet.subset fun i hi => ?_
  by_contra hiF
  exact hi (hF₀ ▸ subset_span ⟨i, hiF, rfl⟩)

/-- `tail:lem:stabilization`: after removing the finitely many exceptions, every
cofinite subfamily spans exactly the cofinite span. -/
theorem span_eq_cofiniteSpan_of_exceptions (v : I → V) (G : Set I) (hG : G.Finite) :
    span M (v '' ({i | v i ∉ cofiniteSpan (M := M) v} ∪ G)ᶜ) = cofiniteSpan (M := M) v := by
  classical
  set E := {i | v i ∉ cofiniteSpan (M := M) v}
  have hE : E.Finite := finite_setOf_not_mem_cofiniteSpan v
  refine le_antisymm (span_le.mpr ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    by_contra h
    exact hi (Or.inl h)
  · have h := cofiniteSpan_le (M := M) v (hE.union hG).toFinset
    rwa [deletedSpan, Set.Finite.coe_toFinset] at h

end Surreal.TailSpan

namespace Surreal.TailSpan

open Module Submodule

section Multilinear

variable {K W J : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- `tail:lem:multilinear`: if every cofinite subfamily spans, a multilinear form
vanishing on all tuples of pairwise distinct members vanishes identically. -/
theorem multilinear_eq_zero_of_distinct {D : ℕ} (w : J → W)
    (hspan : ∀ F : Finset J, span K (w '' (↑F : Set J)ᶜ) = ⊤)
    (T : MultilinearMap K (fun _ : Fin D => W) K)
    (hT : ∀ i : Fin D → J, Function.Injective i → T (fun j => w (i j)) = 0) : T = 0 := by
  classical
  -- Free the arguments one coordinate at a time, from the first upwards.
  have key : ∀ k : ℕ, ∀ (x : Fin D → W) (i : Fin D → J),
      (∀ j₁ j₂ : Fin D, k ≤ (j₁ : ℕ) → k ≤ (j₂ : ℕ) → i j₁ = i j₂ → j₁ = j₂) →
      (∀ j : Fin D, k ≤ (j : ℕ) → x j = w (i j)) → T x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x i hinj hx
      have : x = fun j => w (i j) := funext fun j => hx j (Nat.zero_le _)
      rw [this]
      exact hT i fun j₁ j₂ h => hinj j₁ j₂ (Nat.zero_le _) (Nat.zero_le _) h
    | succ k ih =>
      intro x i hinj hx
      by_cases hk : k < D
      · set c : Fin D := ⟨k, hk⟩
        set F : Finset J := (Finset.univ.filter fun j : Fin D => k + 1 ≤ (j : ℕ)).image i
        have hzero : ∀ m ∉ F, T.toLinearMap x c (w m) = 0 := by
          intro m hm
          rw [MultilinearMap.toLinearMap_apply]
          refine ih (Function.update x c (w m)) (Function.update i c m) ?_ ?_
          · intro j₁ j₂ h₁ h₂ heq
            by_cases e₁ : j₁ = c <;> by_cases e₂ : j₂ = c
            · exact e₁.trans e₂.symm
            · have h₂' : k + 1 ≤ (j₂ : ℕ) := by
                have : (j₂ : ℕ) ≠ k := fun h => e₂ (Fin.ext h)
                omega
              rw [e₁, Function.update_self, Function.update_of_ne e₂] at heq
              exact absurd (heq ▸ Finset.mem_image_of_mem i
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂'⟩)) hm
            · have h₁' : k + 1 ≤ (j₁ : ℕ) := by
                have : (j₁ : ℕ) ≠ k := fun h => e₁ (Fin.ext h)
                omega
              rw [e₂, Function.update_self, Function.update_of_ne e₁] at heq
              exact absurd (heq.symm ▸ Finset.mem_image_of_mem i
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁'⟩)) hm
            · have h₁' : k + 1 ≤ (j₁ : ℕ) := by
                have : (j₁ : ℕ) ≠ k := fun h => e₁ (Fin.ext h)
                omega
              have h₂' : k + 1 ≤ (j₂ : ℕ) := by
                have : (j₂ : ℕ) ≠ k := fun h => e₂ (Fin.ext h)
                omega
              rw [Function.update_of_ne e₁, Function.update_of_ne e₂] at heq
              exact hinj j₁ j₂ h₁' h₂' heq
          · intro j hj
            by_cases e : j = c
            · rw [e, Function.update_self, Function.update_self]
            · have hj' : k + 1 ≤ (j : ℕ) := by
                have : (j : ℕ) ≠ k := fun h => e (Fin.ext h)
                omega
              rw [Function.update_of_ne e, Function.update_of_ne e]
              exact hx j hj'
        have hL : T.toLinearMap x c = 0 := by
          apply LinearMap.ext_on (hspan F)
          rintro _ ⟨m, hm, rfl⟩
          simpa using hzero m (by simpa using hm)
        have := congrArg (fun L => L (x c)) hL
        simpa [MultilinearMap.toLinearMap_apply] using this
      · exact ih x i (fun j₁ j₂ h₁ h₂ => hinj j₁ j₂ (by omega) (by omega))
          (fun j hj => absurd j.2 (by omega))
  ext x
  rcases isEmpty_or_nonempty J with hJ | hJ
  · -- With no indices the empty family spans, so the space is zero.
    have htop : (⊥ : Submodule K W) = ⊤ := by
      rw [← hspan ∅]
      simp [Set.range_eq_empty]
    haveI : Subsingleton W := (Submodule.subsingleton_iff K).mp (subsingleton_of_bot_eq_top htop)
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have hx : x = fun j => w ((finZeroElim : (j : Fin 0) → (fun _ => J) j) j) :=
        funext fun j => j.elim0
      rw [hx]
      exact hT _ fun j => j.elim0
    · haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
      rw [Subsingleton.elim x 0, T.map_zero]
      rfl
  · exact key D x (fun _ => hJ.some) (fun j _ _ => absurd j.2 (by omega))
      (fun j h => absurd j.2 (by omega))

end Multilinear

section BaseChange

variable {M K W J : Type*} [Field M] [Field K] [Algebra M K] [AddCommGroup W] [Module M W]

open TensorProduct in
/-- Cofinite spanning over the coefficient field persists after scalar extension,
as used in `tail:lem:multilinear`. -/
theorem span_baseChange_eq_top (w : J → W) (F : Set J) (h : span M (w '' F) = ⊤) :
    span K ((fun j => (1 : K) ⊗ₜ[M] w j) '' F) = ⊤ := by
  have := Submodule.baseChange_span (R := M) K (w '' F)
  rw [h, Submodule.baseChange_top, Set.image_image] at this
  exact this.symm

open TensorProduct in
/-- `tail:lem:multilinear` in the source's form: the family spans `W` over `M`
after every finite deletion, and the form is `K`-multilinear on `K ⊗ W`. -/
theorem multilinear_baseChange_eq_zero {D : ℕ} (w : J → W)
    (hspan : ∀ F : Finset J, span M (w '' (↑F : Set J)ᶜ) = ⊤)
    (T : MultilinearMap K (fun _ : Fin D => K ⊗[M] W) K)
    (hT : ∀ i : Fin D → J, Function.Injective i → T (fun j => (1 : K) ⊗ₜ[M] w (i j)) = 0) :
    T = 0 :=
  multilinear_eq_zero_of_distinct (fun j => (1 : K) ⊗ₜ[M] w j)
    (fun F => span_baseChange_eq_top w _ (hspan F)) T hT

end BaseChange

end Surreal.TailSpan
