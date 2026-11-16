import PA194TranslateExt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Derivability under domain guards

`GDerivable T Δ`: the source theory derives `Δ` together with the guards `¬Dom(&i)` below
some bound. The bound is existential, so guarded derivations of different sequents combine by
weakening. The quantifier rules are relativized to the domain: the guard of the eigenvariable
of a universal introduction becomes the domain hypothesis of the quantifier, and an
existential introduction with a free variable as witness takes its domain formula from the
guards.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Two syntactic identities -/

theorem free_guardBody_or {p : V} (hp : IsSemiformula SourceL 1 p) :
    free SourceL (guardBody ^⋎ p) = guard 0 ^⋎ free SourceL p := by
  show subst SourceL (?[^&(0 : V)] : V) (shift SourceL (guardBody ^⋎ p)) =
    guard 0 ^⋎ subst SourceL (?[^&(0 : V)] : V) (shift SourceL p)
  rw [shift_or guardBody_valid.isUFormula hp.isUFormula,
    substs_or guardBody_valid.shift.isUFormula hp.shift.isUFormula]
  congr 1
  exact free_guardBody
theorem substs1_domain_and {p : V} (hp : IsSemiformula SourceL 1 p) (j : V) :
    substs1 SourceL (^&j) (domainCode (^#(0 : V)) ^⋏ p) =
      domainCode (^&j) ^⋏ substs1 SourceL (^&j) p := by
  have hw : IsSemitermVec SourceL 1 0 (?[^&j] : V) := by simp
  show subst SourceL (?[^&j] : V) (domainCode (^#(0 : V)) ^⋏ p) =
    domainCode (^&j) ^⋏ subst SourceL (?[^&j] : V) p
  rw [substs_and domainBody_valid.isUFormula hp.isUFormula,
    domainCode_subst (show IsSemiterm SourceL 1 (^#(0 : V)) by simp) hw, termSubst_bvar]
  simp

theorem guards_union_insert_subset {n m p Δ : V} (hnm : n ≤ m) :
    guards n ∪ insert p Δ ⊆ insert p (guards m ∪ Δ) := by
  intro x hx
  rcases mem_cup_iff.mp hx with h | h
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl (guards_mono hnm h))))
  · rcases mem_bitInsert_iff.mp h with h | h
    · exact mem_bitInsert_iff.mpr (Or.inl h)
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr h)))
theorem guards_union_subset {n m Δ Δ' : V} (hnm : n ≤ m) (h : Δ ⊆ Δ') :
    guards n ∪ Δ ⊆ guards m ∪ Δ' := by
  intro x hx
  rcases mem_cup_iff.mp hx with hx | hx
  · exact mem_cup_iff.mpr (Or.inl (guards_mono hnm hx))
  · exact mem_cup_iff.mpr (Or.inr (h hx))

variable (T : Theory SourceL) [T.Δ₁]

/-- Derivability in `T` together with the guards below some bound. -/
def GDerivable (Δ : V) : Prop := ∃ n, Derivable T (guards n ∪ Δ)

namespace GDerivable
variable {T}

theorem isFormulaSet {Δ : V} (h : GDerivable T Δ) : IsFormulaSet SourceL Δ := by
  obtain ⟨n,h⟩ := h
  exact (IsFormulaSet.union.mp h.isFormulaSet).2

theorem wk {Δ Δ' : V} (hΔ' : IsFormulaSet SourceL Δ') (hsub : Δ ⊆ Δ') (h : GDerivable T Δ) :
    GDerivable T Δ' := by
  obtain ⟨n,h⟩ := h
  exact ⟨n,Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid n,hΔ'⟩)
    (guards_union_subset le_rfl hsub) h⟩

theorem em {Δ : V} (hΔ : IsFormulaSet SourceL Δ) (p : V) (h : p ∈ Δ) (hn : neg SourceL p ∈ Δ) :
    GDerivable T Δ :=
  ⟨0,Derivable.em (IsFormulaSet.union.mpr ⟨guards_valid 0,hΔ⟩) p
    (mem_cup_iff.mpr (Or.inr h)) (mem_cup_iff.mpr (Or.inr hn))⟩

theorem verum {Δ : V} (hΔ : IsFormulaSet SourceL Δ) (h : ^⊤ ∈ Δ) : GDerivable T Δ :=
  ⟨0,Derivable.verum (IsFormulaSet.union.mpr ⟨guards_valid 0,hΔ⟩) (mem_cup_iff.mpr (Or.inr h))⟩

/-- A premise with one more formula, under the guards of a larger bound. -/
theorem lift {n m p Δ : V} (hnm : n ≤ m) (h : Derivable T (guards n ∪ insert p Δ)) :
    Derivable T (insert p (guards m ∪ Δ)) := by
  have hs := (IsFormulaSet.union.mp h.isFormulaSet).2
  have hp := (IsFormulaSet.insert_iff.mp hs).1
  have hΔ := (IsFormulaSet.insert_iff.mp hs).2
  exact Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hp,IsFormulaSet.union.mpr ⟨guards_valid m,hΔ⟩⟩)
    (guards_union_insert_subset hnm) h

theorem and_m {Δ p q : V} (hmem : p ^⋏ q ∈ Δ) (hp : GDerivable T (insert p Δ))
    (hq : GDerivable T (insert q Δ)) : GDerivable T Δ := by
  obtain ⟨n₁,hp⟩ := hp
  obtain ⟨n₂,hq⟩ := hq
  exact ⟨max n₁ n₂,Derivable.and_m (mem_cup_iff.mpr (Or.inr hmem))
    (lift (le_max_left n₁ n₂) hp) (lift (le_max_right n₁ n₂) hq)⟩

theorem or_m {Δ p q : V} (hmem : p ^⋎ q ∈ Δ) (h : GDerivable T (insert p (insert q Δ))) :
    GDerivable T Δ := by
  obtain ⟨n,h⟩ := h
  have hs := (IsFormulaSet.union.mp h.isFormulaSet).2
  have hp := (IsFormulaSet.insert_iff.mp hs).1
  have hs' := (IsFormulaSet.insert_iff.mp hs).2
  have hq := (IsFormulaSet.insert_iff.mp hs').1
  have hΔ := (IsFormulaSet.insert_iff.mp hs').2
  refine ⟨n,Derivable.or_m (mem_cup_iff.mpr (Or.inr hmem)) ?_⟩
  refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hp,IsFormulaSet.insert_iff.mpr
    ⟨hq,IsFormulaSet.union.mpr ⟨guards_valid n,hΔ⟩⟩⟩) ?_ h
  intro x hx
  rcases mem_cup_iff.mp hx with hx | hx
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hx)))))
  · rcases mem_bitInsert_iff.mp hx with hx | hx
    · exact mem_bitInsert_iff.mpr (Or.inl hx)
    · rcases mem_bitInsert_iff.mp hx with hx | hx
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl hx)))
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr hx)))))

theorem cut {Δ : V} (p : V) (h₁ : GDerivable T (insert p Δ))
    (h₂ : GDerivable T (insert (neg SourceL p) Δ)) : GDerivable T Δ := by
  obtain ⟨n₁,h₁⟩ := h₁
  obtain ⟨n₂,h₂⟩ := h₂
  exact ⟨max n₁ n₂,Derivable.cut p (lift (le_max_left n₁ n₂) h₁) (lift (le_max_right n₁ n₂) h₂)⟩

theorem shift {Δ : V} (h : GDerivable T Δ) : GDerivable T (setShift SourceL Δ) := by
  have hΔ := h.isFormulaSet
  obtain ⟨n,h⟩ := h
  refine ⟨n+1,Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid _,hΔ.setShift⟩) ?_
    (Derivable.shift h)⟩
  intro x hx
  rw [mem_setShift_union] at hx
  rcases mem_cup_iff.mp hx with hx | hx
  · exact mem_cup_iff.mpr (Or.inl (setShift_guards_subset n hx))
  · exact mem_cup_iff.mpr (Or.inr hx)

/-- Universal introduction relativized to the domain. -/
theorem all_rel {Δ p : V} (hp : IsSemiformula SourceL 1 p) (hmem : ^∀ (guardBody ^⋎ p) ∈ Δ)
    (h : GDerivable T (insert (free SourceL p) (setShift SourceL Δ))) : GDerivable T Δ := by
  have hs := h.isFormulaSet
  obtain ⟨n,h⟩ := h
  have hfp : IsFormula SourceL (free SourceL p) := hp.free
  have hΔs : IsFormulaSet SourceL (setShift SourceL Δ) := (IsFormulaSet.insert_iff.mp hs).2
  have hΔ : IsFormulaSet SourceL Δ := IsFormulaSet.setShift_iff.mp hΔs
  have hΓ : IsFormulaSet SourceL (guards n ∪ Δ) := IsFormulaSet.union.mpr ⟨guards_valid n,hΔ⟩
  refine ⟨n,Derivable.all_m (p := guardBody ^⋎ p) (mem_cup_iff.mpr (Or.inr hmem)) ?_⟩
  rw [free_guardBody_or hp]
  refine Derivable.or_m (p := guard 0) (q := free SourceL p) (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_
  refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨guard_valid 0,IsFormulaSet.insert_iff.mpr
    ⟨hfp,IsFormulaSet.insert_iff.mpr ⟨IsSemiformula.or.mpr ⟨guard_valid 0,hfp⟩,hΓ.setShift⟩⟩⟩) ?_ h
  intro x hx
  rcases mem_cup_iff.mp hx with hx | hx
  · have hx' := guards_succ_subset n (guards_mono (show n ≤ n + 1 by simp) hx)
    rcases mem_bitInsert_iff.mp hx' with hx' | hx'
    · exact mem_bitInsert_iff.mpr (Or.inl hx')
    · refine mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
        (mem_bitInsert_iff.mpr (Or.inr ?_)))))
      rw [mem_setShift_union]
      exact mem_cup_iff.mpr (Or.inl hx')
  · rcases mem_bitInsert_iff.mp hx with hx | hx
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl hx)))
    · refine mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
        (mem_bitInsert_iff.mpr (Or.inr ?_)))))
      rw [mem_setShift_union]
      exact mem_cup_iff.mpr (Or.inr hx)

/-- Existential introduction relativized to the domain, with a free variable as witness. -/
theorem ex_rel {Δ p : V} (hp : IsSemiformula SourceL 1 p)
    (hmem : ^∃ (domainCode (^#(0 : V)) ^⋏ p) ∈ Δ) (j : V)
    (h : GDerivable T (insert (substs1 SourceL (^&j) p) Δ)) : GDerivable T Δ := by
  have hs := h.isFormulaSet
  obtain ⟨n,h⟩ := h
  have hjterm : IsTerm SourceL (^&j : V) := by simp
  have hpj : IsFormula SourceL (substs1 SourceL (^&j) p) := (IsFormulaSet.insert_iff.mp hs).1
  have hΔ : IsFormulaSet SourceL Δ := (IsFormulaSet.insert_iff.mp hs).2
  have hDj : IsFormula SourceL (domainCode (^&j : V)) := domainCode_valid hjterm
  have hand : IsFormula SourceL (domainCode (^&j : V) ^⋏ substs1 SourceL (^&j) p) :=
    IsSemiformula.and.mpr ⟨hDj,hpj⟩
  have hΓ : IsFormulaSet SourceL (guards (max n (j+1)) ∪ Δ) :=
    IsFormulaSet.union.mpr ⟨guards_valid _,hΔ⟩
  refine ⟨max n (j+1),Derivable.ex_m (p := domainCode (^#(0 : V)) ^⋏ p) (t := ^&j)
    (mem_cup_iff.mpr (Or.inr hmem)) hjterm ?_⟩
  rw [substs1_domain_and hp j]
  refine Derivable.and_m (p := domainCode (^&j : V)) (q := substs1 SourceL (^&j) p)
    (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_ ?_
  · refine Derivable.em (IsFormulaSet.insert_iff.mpr ⟨hDj,IsFormulaSet.insert_iff.mpr ⟨hand,hΓ⟩⟩)
      (domainCode (^&j)) (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_
    exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
      (Or.inl (mem_guards.mpr ⟨j,lt_of_lt_of_le (lt_add_one j) (le_max_right n (j+1)),rfl⟩))))))
  · refine Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hpj,IsFormulaSet.insert_iff.mpr ⟨hand,hΓ⟩⟩)
      ?_ h
    intro x hx
    rcases mem_cup_iff.mp hx with hx | hx
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
        (Or.inl (guards_mono (le_max_left n (j+1)) hx))))))
    · rcases mem_bitInsert_iff.mp hx with hx | hx
      · exact mem_bitInsert_iff.mpr (Or.inl hx)
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
          (mem_cup_iff.mpr (Or.inr hx)))))

/-- A guarded refutation is a refutation when the domain is inhabited. -/
theorem root (hdom : Provable T (^∃ (domainCode (^#(0 : V)))))
    (h : GDerivable T ({(^⊥ : V)} : V)) : Provable T (^⊥ : V) := by
  obtain ⟨n,h⟩ := h
  exact discharge_guards T hdom n h

end GDerivable

#print axioms GDerivable.cut
#print axioms GDerivable.shift
#print axioms GDerivable.all_rel
#print axioms GDerivable.ex_rel
#print axioms GDerivable.root
end generic
end PA194GuardedCompiler
