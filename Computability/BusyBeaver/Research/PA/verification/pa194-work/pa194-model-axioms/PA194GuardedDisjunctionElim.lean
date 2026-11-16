import PA194UniqueVariableOpen
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-- Invert a translated disjunction in a guarded proof. -/
theorem guarded_or_unpack_context {a b Γ : V} (ha : IsFormula SourceL a) (hb : IsFormula SourceL b)
    (hΓ : IsFormulaSet SourceL Γ) (h : GDerivable T (insert (a ^⋎ b) Γ)) :
    GDerivable T (insert a (insert b Γ)) := by
  let q : V := a ^⋎ b
  let Δ : V := insert a (insert b Γ)
  have hq : IsFormula SourceL q := IsSemiformula.or.mpr ⟨ha,hb⟩
  have hna : IsFormula SourceL (neg SourceL a) := IsSemiformula.neg_iff.mpr ha
  have hnb : IsFormula SourceL (neg SourceL b) := IsSemiformula.neg_iff.mpr hb
  have hΔ : IsFormulaSet SourceL Δ := fs_cons ha (fs_cons hb hΓ)
  change GDerivable T Δ
  apply GDerivable.cut_wk hΔ hq h
    (Δ₂ := insert (neg SourceL q) Δ) ?_ (by dsimp [q,Δ]; set_tac) (by intro x hx; exact hx)
  have hn : neg SourceL q = neg SourceL a ^⋏ neg SourceL b := by
    exact neg_or ha.isUFormula hb.isUFormula
  rw [hn]
  have h1 : GDerivable T (insert (neg SourceL a) (insert (neg SourceL a ^⋏ neg SourceL b) Δ)) := by
    apply GDerivable.em (fs_cons hna (fs_cons (IsSemiformula.and.mpr ⟨hna,hnb⟩) hΔ)) a
    · dsimp [Δ]; simp
    · simp
  have h2 : GDerivable T (insert (neg SourceL b) (insert (neg SourceL a ^⋏ neg SourceL b) Δ)) := by
    apply GDerivable.em (fs_cons hnb (fs_cons (IsSemiformula.and.mpr ⟨hna,hnb⟩) hΔ)) b
    · dsimp [Δ]; simp
    · simp
  exact GDerivable.and_m (by simp) h1 h2


/-- Invert a translated disjunction in a guarded proof. -/
theorem guarded_or_unpack {a b : V} (ha : IsFormula SourceL a) (hb : IsFormula SourceL b)
    (h : GDerivable T ({a ^⋎ b} : V)) : GDerivable T (insert a ({b} : V)) := by
  let q : V := a ^⋎ b
  let Δ : V := insert a ({b} : V)
  have hq : IsFormula SourceL q := IsSemiformula.or.mpr ⟨ha,hb⟩
  have hna : IsFormula SourceL (neg SourceL a) := IsSemiformula.neg_iff.mpr ha
  have hnb : IsFormula SourceL (neg SourceL b) := IsSemiformula.neg_iff.mpr hb
  have hΔ : IsFormulaSet SourceL Δ := fs_cons ha (by rw [singleton_eq_insert]; exact fs_cons hb fs_nil)
  change GDerivable T Δ
  apply GDerivable.cut_wk hΔ hq h
    (Δ₂ := insert (neg SourceL q) Δ) ?_ (by dsimp [q,Δ]; set_tac) (by intro x hx; exact hx)
  have hn : neg SourceL q = neg SourceL a ^⋏ neg SourceL b := by
    exact neg_or ha.isUFormula hb.isUFormula
  rw [hn]
  have h1 : GDerivable T (insert (neg SourceL a) (insert (neg SourceL a ^⋏ neg SourceL b) Δ)) := by
    apply GDerivable.em (fs_cons hna (fs_cons (IsSemiformula.and.mpr ⟨hna,hnb⟩) hΔ)) a
    · dsimp [Δ]; simp
    · simp
  have h2 : GDerivable T (insert (neg SourceL b) (insert (neg SourceL a ^⋏ neg SourceL b) Δ)) := by
    apply GDerivable.em (fs_cons hnb (fs_cons (IsSemiformula.and.mpr ⟨hna,hnb⟩) hΔ)) b
    · dsimp [Δ]; simp
    · simp
  exact GDerivable.and_m (by simp) h1 h2

#print axioms guarded_or_unpack_context
#print axioms guarded_or_unpack
end generic
end PA194GuardedCompiler
