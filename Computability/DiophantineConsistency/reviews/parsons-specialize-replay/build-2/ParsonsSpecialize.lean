import DiophantineConsistency.ParsonsCollectionSemantic
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsSpecialize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule
variable {L : Language}

theorem subst_after_shift {n : ℕ} (v : Fin (n+1) → SyntacticTerm L) :
    (Rew.subst v).comp (@Rew.bShift L ℕ n) = Rew.subst (fun i : Fin n => v i.succ) := by
  ext i <;> simp [Rew.comp_app]

theorem subst_qpow_last : (n : ℕ) → (v : Fin (1+n) → SyntacticTerm L) →
    (Rew.subst (fun i : Fin (0+n) => v ⟨i.val, by omega⟩)).comp
      ((Rew.subst ![v ⟨n, by omega⟩]).qpow n) =
      Rew.subst v
  | 0, v => by
      ext i
      · have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
        subst i
        simp
      · simp
  | n+1, v => by
      ext i
      · cases i using Fin.cases with
        | zero => simp [Rew.comp_app, Rew.qpow_succ]
        | succ i =>
          simp only [Rew.comp_app, Rew.qpow_succ, Rew.q_bvar_succ]
          have hs : (Rew.subst (fun j : Fin (0+(n+1)) => v ⟨j.val, by omega⟩)).comp
              (@Rew.bShift L ℕ (0+n)) =
              Rew.subst (fun j : Fin (0+n) => v ⟨j.val+1, by omega⟩) := by
            ext j <;> simp [Rew.comp_app]
          have hterm := Rew.ext' hs (((Rew.subst ![v ⟨n+1, by omega⟩]).qpow n) #i)
          simp only [Rew.comp_app] at hterm
          rw [hterm]
          have ih := Rew.ext' (subst_qpow_last n (fun j => v ⟨j.val+1, by omega⟩)) (#i)
          have hin : i.val < n+1 := by simpa [Nat.add_comm] using i.isLt
          have hv : (⟨i.val+1, by omega⟩ : Fin (1+(n+1))) = i.succ := Fin.ext (by simp)
          simpa [Rew.comp_app, hv] using ih
      · simp only [Rew.comp_app, Rew.qpow_succ, Rew.q_fvar]
        have hs : (Rew.subst (fun j : Fin (0+(n+1)) => v ⟨j.val, by omega⟩)).comp
              (@Rew.bShift L ℕ (0+n)) =
              Rew.subst (fun j : Fin (0+n) => v ⟨j.val+1, by omega⟩) := by
            ext j <;> simp [Rew.comp_app]
        have hterm := Rew.ext' hs (((Rew.subst ![v ⟨n+1, by omega⟩]).qpow n) &i)
        simp only [Rew.comp_app] at hterm
        rw [hterm]
        have ih := Rew.ext' (subst_qpow_last n (fun j => v ⟨j.val+1, by omega⟩)) (&i)
        simpa [Rew.comp_app] using ih

theorem all_closure_outer {n : ℕ} (A : Semiformula L ℕ (1+n)) :
    (∀⁰* A) = ∀⁰ (∀⁰^[n] A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allClosure_succ, allItr_succ]
    exact ih (∀⁰ A)

theorem all_itr_closure {n : ℕ} (A : Semiformula L ℕ (0+n)) :
    (∀⁰^[n] A) = ∀⁰* A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allClosure_succ, allItr_succ]
    exact ih (∀⁰ A)

theorem closure_cast {n m : ℕ} (e : n = m) (A : Semiformula L ℕ n) :
    (∀⁰* (cast (congrArg (Semiformula L ℕ) e) A)) = ∀⁰* A := by
  cases e; rfl

theorem subst_cast {n m : ℕ} (e : n = m) (A : Semiformula L ℕ n)
    (v : Fin n → SyntacticTerm L) :
    (cast (congrArg (Semiformula L ℕ) e) A) ⇜
      (cast (congrArg (fun k => Fin k → SyntacticTerm L) e) v) = A ⇜ v := by
  cases e; rfl

variable [L.ORing]

def specialize_closure {T : Theory L} : (n : ℕ) →
    (A : Semiformula L ℕ (0+n)) → (v : Fin (0+n) → SyntacticTerm L) →
    Proof T (∀⁰* A) → Proof T (A ⇜ v)
  | 0, A, v, h => by simpa [Rewriting.subst] using h
  | n+1, A, v, h => by
    let e : 0+(n+1) = 1+n := by omega
    let A' : Semiformula L ℕ (1+n) := cast (congrArg (Semiformula L ℕ) e) A
    let v' : Fin (1+n) → SyntacticTerm L := cast (congrArg (fun k => Fin k → SyntacticTerm L) e) v
    have hh : Proof T (∀⁰ (∀⁰^[n] A')) := by
      rw [← all_closure_outer]
      change Proof T (∀⁰* cast (congrArg (Semiformula L ℕ) e) A)
      rw [closure_cast e A]
      exact h
    let last := v' ⟨n, by omega⟩
    let next : Semiformula L ℕ (0+n) := (Rew.subst ![last]).qpow n ▹ A'
    have hn : Proof T (∀⁰* next) := by
      simpa [next, Rewriting.subst, all_itr_closure] using (Proof.specialize last hh)
    let vrest : Fin (0+n) → SyntacticTerm L := fun i => v' ⟨i.val, by omega⟩
    have hp := specialize_closure n next vrest hn
    have he : next ⇜ vrest = A' ⇜ v' := by
      simp [next, vrest, last, Rewriting.subst, ← TransitiveRewriting.comp_app, subst_qpow_last]
    rw [he] at hp
    change Proof T ((cast (congrArg (Semiformula L ℕ) e) A) ⇜
      (cast (congrArg (fun k => Fin k → SyntacticTerm L) e) v)) at hp
    rw [subst_cast e A v] at hp
    exact hp

/-- Specialize the universal closure at the original free variables. -/
def specialize_univCl {T : Theory L} (P : Proposition L)
    (h : Proof T (P.univCl : Proposition L)) : Proof T P := by
  have hh : Proof T (∀⁰* (Rew.fixitr 0 P.fvSup ▹ P)) := by
    simpa [Semiformula.univCl'] using h
  have ht := specialize_closure P.fvSup (Rew.fixitr 0 P.fvSup ▹ P)
    (fun i => (&↑i : SyntacticTerm L)) hh
  simpa using ht

/-- The full Σ₁ collection-rule transformer, with arbitrary free parameters. -/
noncomputable def collect (D : ArithmeticSemiformula ℕ 2)
    (hD : Hierarchy 𝚺 1 D) (hTotal : Proof 𝗣𝗔⁻ (ParsonsCollectionRule.total D)) :
    Proof 𝗣𝗔⁻ (∀⁰ ParsonsCollectionRule.collector D) := by
  let P : ArithmeticSemiformula ℕ 0 := ParsonsCollectionRule.total D 🡒
    step (ParsonsCollectionRule.collector D)
  have hClosed : Proof 𝗣𝗔⁻ (P.univCl : Proposition ℒₒᵣ) := by
    exact ParsonsRuleEmbedding.embedTheory (ParsonsCollectionSemantic.step_closed D).some
  have hStep : Proof 𝗣𝗔⁻ P := specialize_univCl P hClosed
  exact ParsonsCollectionRule.collect_if_step D hD hTotal hStep

end DiophantineConsistency.ParsonsSpecialize
