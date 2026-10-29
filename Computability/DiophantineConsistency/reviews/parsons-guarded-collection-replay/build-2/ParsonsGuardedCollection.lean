import DiophantineConsistency.ParsonsSpecialize
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardedCollection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsCollectionRule ParsonsSpecialize

def restricted (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2) : Proposition ℒₒᵣ :=
  “∀ i, !K i → ∃ y, !D i y”

def strippedMatrix (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2) :
    Semiproposition ℒₒᵣ 2 := (Rew.bShift.q ▹ K) 🡒 D

def guardMatrix (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2)
    (E : Proposition ℒₒᵣ) : Semiproposition ℒₒᵣ 2 :=
  strippedMatrix K D ⋎ (Rew.bShift ▹ (Rew.bShift ▹ E))

theorem guard_sigma (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2)
    (E : Proposition ℒₒᵣ) (hK : Hierarchy 𝚺 0 K) (hD : Hierarchy 𝚺 1 D)
    (hE : Hierarchy 𝚺 1 E) : Hierarchy 𝚺 1 (guardMatrix K D E) := by
  have hk : Hierarchy 𝚷 1 K := hK.of_zero
  simp [guardMatrix, strippedMatrix, hk, hD, hE]

theorem guard_semantics (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2)
    (E : Proposition ℒₒᵣ) (M : Type) [ORingStructure M]
    (f : ℕ → M) :
    (E ⋎ restricted K D).Evalf f → (total (guardMatrix K D E)).Evalf f := by
  classical
  simp [restricted, total, guardMatrix, strippedMatrix, Semiformula.imp_eq,
    Semiformula.eval_rew, Function.comp_def, Matrix.fun_eq_vec_two,
    Matrix.constant_eq_singleton, Matrix.empty_eq]
  intro h x
  rcases h with he | ha
  · exact ⟨0, Or.inr he⟩
  · rcases ha x with hk | ⟨y, hy⟩
    · exact ⟨0, Or.inl (Or.inl hk)⟩
    · exact ⟨y, Or.inl (Or.inr hy)⟩

theorem unguard_semantics (K : ArithmeticSemiformula ℕ 1) (D : ArithmeticSemiformula ℕ 2)
    (E : Proposition ℒₒᵣ) (M : Type) [ORingStructure M] (f : ℕ → M)
    (h : (∀⁰ collector (guardMatrix K D E)).Evalf f) :
    (E ⋎ (∀⁰ collector (strippedMatrix K D))).Evalf f := by
  classical
  by_cases he : E.Evalf f
  · simp [he]
  · simp [collector, guardMatrix, strippedMatrix, Semiformula.imp_eq,
      Semiformula.eval_rew, Function.comp_def, Matrix.fun_eq_vec_two,
      Matrix.constant_eq_singleton, Matrix.empty_eq, he] at h ⊢
    exact h

/-- A semantic implication valid in every PA-minus model yields a rule proof
of the corresponding open implication, specializing all free parameters. -/
noncomputable def of_semantics (P Q : Proposition ℒₒᵣ)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      ∀ f : ℕ → M, P.Evalf f → Q.Evalf f) : Proof 𝗣𝗔⁻ (P 🡒 Q) := by
  have hp : 𝗣𝗔⁻ ⊢ (P 🡒 Q).univCl := by
    apply Arithmetic.complete.{0}
    intro M _ _
    simp only [models_iff, Semiformula.eval_univCl]
    intro f
    classical
    by_cases hP : P.Evalf f
    · simp [Semiformula.imp_eq, hP, h M f hP]
    · simp [Semiformula.imp_eq, hP]
  exact specialize_univCl (P 🡒 Q) (ParsonsRuleEmbedding.embedTheory hp.some)

/-- Collection is admissible under an arbitrary Σ₁ positive side guard.
The outer predicate K is bounded, D and E are Σ₁, and all free parameters
are retained. The input is a proof, not an assumed collection implication. -/
noncomputable def guarded_collect (K : ArithmeticSemiformula ℕ 1)
    (D : ArithmeticSemiformula ℕ 2) (E : Proposition ℒₒᵣ)
    (hK : Hierarchy 𝚺 0 K) (hD : Hierarchy 𝚺 1 D) (hE : Hierarchy 𝚺 1 E)
    (h : Proof 𝗣𝗔⁻ (E ⋎ restricted K D)) :
    Proof 𝗣𝗔⁻ (E ⋎ (∀⁰ collector (strippedMatrix K D))) := by
  let P := E ⋎ restricted K D
  let Q := total (guardMatrix K D E)
  have hPQ : Proof 𝗣𝗔⁻ (P 🡒 Q) := of_semantics P Q (by
    intro M _ _ f
    exact guard_semantics K D E M f)
  have htotal : Proof 𝗣𝗔⁻ Q := .mp hPQ h
  have hbounded : Proof 𝗣𝗔⁻ (∀⁰ collector (guardMatrix K D E)) :=
    collect (guardMatrix K D E) (guard_sigma K D E hK hD hE) htotal
  have hback : Proof 𝗣𝗔⁻ ((∀⁰ collector (guardMatrix K D E)) 🡒
      (E ⋎ (∀⁰ collector (strippedMatrix K D)))) := of_semantics _ _ (by
    intro M _ _ f
    exact unguard_semantics K D E M f)
  exact .mp hback hbounded

theorem restricted_outer (D : ArithmeticSemiformula ℕ 2) (n : SyntacticTerm ℒₒᵣ) :
    restricted (ParsonsCollection.outerGuard n) D = ParsonsCollection.unbounded D n := by
  simp [restricted, ParsonsCollection.outerGuard, ParsonsCollection.unbounded,
    Semiformula.ballLT, ball]

theorem outerGuard_bounded (n : SyntacticTerm ℒₒᵣ) :
    Hierarchy 𝚺 0 (ParsonsCollection.outerGuard n) := by
  simp [ParsonsCollection.outerGuard]

theorem strip_to_collection (D : ArithmeticSemiformula ℕ 2) (n : SyntacticTerm ℒₒᵣ)
    (E : Proposition ℒₒᵣ) (M : Type) [ORingStructure M] (f : ℕ → M)
    (h : (E ⋎ (∀⁰ collector (strippedMatrix (ParsonsCollection.outerGuard n) D))).Evalf f) :
    (E ⋎ ParsonsCollection.collection D n).Evalf f := by
  classical
  by_cases he : E.Evalf f
  · simp [he]
  · simp [collector, strippedMatrix, ParsonsCollection.outerGuard,
      ParsonsCollection.collection, Semiformula.imp_eq, Semiformula.eval_rew,
      Semiterm.val_rew, Function.comp_def, Matrix.fun_eq_vec_two, Matrix.empty_eq, he] at h ⊢
    obtain ⟨B, hB⟩ := h (Semiterm.val ![] f n)
    refine ⟨B, ?_⟩
    intro i hi
    obtain ⟨y, hy, hd⟩ := hB i hi
    exact ⟨y, hy, hd.resolve_left (fun hn => hn hi)⟩

/-- The concrete positive-guarded collection transformation. It accepts an
actual proof of `E ∨ ∀i<n ∃y D(i,y)` and returns an actual proof of
`E ∨ ∃B∀i<n∃y<B D(i,y)`, with all parameters retained. -/
noncomputable def guarded_bounded (D : ArithmeticSemiformula ℕ 2)
    (n : SyntacticTerm ℒₒᵣ) (E : Proposition ℒₒᵣ)
    (hD : Hierarchy 𝚺 1 D) (hE : Hierarchy 𝚺 1 E)
    (h : Proof 𝗣𝗔⁻ (E ⋎ ParsonsCollection.unbounded D n)) :
    Proof 𝗣𝗔⁻ (E ⋎ ParsonsCollection.collection D n) := by
  let K := ParsonsCollection.outerGuard n
  have hi : Proof 𝗣𝗔⁻ (E ⋎ restricted K D) := by
    simpa [K, restricted_outer] using h
  have hc : Proof 𝗣𝗔⁻ (E ⋎ (∀⁰ collector (strippedMatrix K D))) :=
    guarded_collect K D E (outerGuard_bounded n) hD hE hi
  have hf : Proof 𝗣𝗔⁻ ((E ⋎ (∀⁰ collector (strippedMatrix K D))) 🡒
      (E ⋎ ParsonsCollection.collection D n)) := of_semantics _ _ (by
    intro M _ _ f
    exact strip_to_collection D n E M f)
  exact .mp hf hc

end DiophantineConsistency.ParsonsGuardedCollection
