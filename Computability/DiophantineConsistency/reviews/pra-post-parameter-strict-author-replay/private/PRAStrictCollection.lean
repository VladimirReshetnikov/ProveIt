import DiophantineConsistency.PRAStrictTheoryComparison
import DiophantineConsistency.ParsonsCollectionSemantic
import DiophantineConsistency.ParsonsGuardedCollection
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAStrictCollection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAStrictSigmaFiniteClient PRAStrictTheoryComparison ParsonsRule ParsonsCollectionRule ParsonsCollectionSemantic
  ParsonsCollection ParsonsGuardedCollection

theorem collector_strict (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D) :
    StrictCase (collector D) := by
  right
  unfold collector
  refine ⟨_, ?_, rfl⟩
  simp [hD]
theorem semantic_base (D : ArithmeticSemiformula ℕ 2) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (f : ℕ → M) : (base (collector D)).Evalf f := by
  simp [base, collector, Semiformula.eval_substs, Semiformula.eval_rew_q, Function.comp_def]
  refine ⟨0, ?_⟩
  intro i hi
  simp [Semiterm.Operator.val, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.Zero.zero, Semiterm.val_func] at hi

theorem semantic_total_collect (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* strictTheory] (f : ℕ → M)
    (ht : (total D).Evalf f) : (∀⁰ collector D).Evalf f := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
    constructor
    intro σ hσ
    exact (inferInstance : M↓[ℒₒᵣ] ⊧* strictTheory).models _ (Or.inl hσ)
  have hind : M↓[ℒₒᵣ] ⊧ (succInd (collector D)).univCl :=
    (inferInstance : M↓[ℒₒᵣ] ⊧* strictTheory).models _
      (Or.inr ⟨collector D,collector_strict D hD,rfl⟩)
  simp only [models_iff, Semiformula.eval_univCl] at hind
  have hb := semantic_base D M f
  have hs := semantic_step D M f ht
  have hi := hind f
  classical
  simp [succInd, Semiformula.imp_eq] at hi
  simp [base] at hb
  simp [step, Semiformula.imp_eq] at hs
  rcases hi with hn | ⟨x,hx,hn⟩ | hall
  · exact False.elim (hn hb)
  · exact False.elim (hn ((hs x).resolve_left (fun h => h hx)))
  · simpa using hall

theorem total_collect (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D) :
    strictTheory ⊢ (total D 🡒 ∀⁰ collector D).univCl := by
  letI : 𝗣𝗔⁻ ⪯ strictTheory := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl h)
  letI : 𝗘𝗤 ℒₒᵣ ⪯ strictTheory := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  classical
  by_cases ht : (total D).Evalf f
  · simp [Semiformula.imp_eq,ht,semantic_total_collect D hD M f ht]
  · simp [Semiformula.imp_eq,ht]
theorem guard_bounded (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (n : SyntacticTerm ℒₒᵣ) :
    Hierarchy 𝚺 0 (guardMatrix (outerGuard n) D (⊥ : Proposition ℒₒᵣ)) := by
  simp [guardMatrix, strippedMatrix, outerGuard, hD]

theorem semantic_bounded_collect (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (n : SyntacticTerm ℒₒᵣ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* strictTheory]
    (f : ℕ → M) (hu : (unbounded D n).Evalf f) : (collection D n).Evalf f := by
  let K := outerGuard n
  let E : Proposition ℒₒᵣ := ⊥
  have hp : (E ⋎ restricted K D).Evalf f := by
    simpa [E,K,restricted_outer] using hu
  have ht := guard_semantics K D E M f hp
  have hc := semantic_total_collect (guardMatrix K D E) (guard_bounded D hD n) M f ht
  have hs := unguard_semantics K D E M f hc
  have hf := strip_to_collection D n E M f (by simpa [K] using hs)
  simpa [E] using hf

/-- Strict existential-bounded induction proves the bounded-collection
implication for every bounded matrix, with arbitrary free parameters. -/
theorem bounded_collect (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (n : SyntacticTerm ℒₒᵣ) : strictTheory ⊢ (unbounded D n 🡒 collection D n).univCl := by
  letI : 𝗣𝗔⁻ ⪯ strictTheory := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl h)
  letI : 𝗘𝗤 ℒₒᵣ ⪯ strictTheory := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  classical
  by_cases hu : (unbounded D n).Evalf f
  · simp [Semiformula.imp_eq,hu,semantic_bounded_collect D hD n M f hu]
  · simp [Semiformula.imp_eq,hu]
theorem semantic_collection_reverse (D : ArithmeticSemiformula ℕ 2) (n : SyntacticTerm ℒₒᵣ)
    (M : Type) [ORingStructure M] (f : ℕ → M)
    (h : (collection D n).Evalf f) : (unbounded D n).Evalf f := by
  simp [collection,unbounded,Semiformula.eval_rew,Function.comp_def,
    Matrix.fun_eq_vec_two] at h ⊢
  obtain ⟨B,hB⟩ := h
  intro i hi
  obtain ⟨y,_,hy⟩ := hB i hi
  exact ⟨y,hy⟩

theorem bounded_collect_iff (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (n : SyntacticTerm ℒₒᵣ) : strictTheory ⊢ (unbounded D n 🡘 collection D n).univCl := by
  letI : 𝗣𝗔⁻ ⪯ strictTheory := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl h)
  letI : 𝗘𝗤 ℒₒᵣ ⪯ strictTheory := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  have h1 := semantic_bounded_collect D hD n M f
  have h2 := semantic_collection_reverse D n M f
  classical
  change ((unbounded D n 🡒 collection D n).Evalf f) ∧
    ((collection D n 🡒 unbounded D n).Evalf f)
  constructor
  · by_cases hu : (unbounded D n).Evalf f
    · simp [Semiformula.imp_eq,hu,h1 hu]
    · simp [Semiformula.imp_eq,hu]
  · by_cases hc : (collection D n).Evalf f
    · simp [Semiformula.imp_eq,hc,h2 hc]
    · simp [Semiformula.imp_eq,hc]
end DiophantineConsistency.PRAStrictCollection
