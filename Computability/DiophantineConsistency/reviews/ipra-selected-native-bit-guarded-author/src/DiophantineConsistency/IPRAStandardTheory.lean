import DiophantineConsistency.IPRASuccessorInductionConverse
/-! # A standard presentation of intuitionistic primitive recursive arithmetic

`standardTheory` is the textbook presentation of iPRA in the full
primitive-recursive function-code language: intuitionistic predicate logic,
reflexivity of equality together with replacement `x = y → A(x) → A(y)` for
*atomic* `A` only, the defining equations of every primitive-recursive code,
`S x ≠ 0`, `S x = S y → x = y`, the explicit definition of the extra relation
symbol `<` by its characteristic code, and the successor-form induction axiom
`A(0) → ∀x (A(x) → A(S x)) → ∀x A(x)` for every quantifier-free `A` with
arbitrary parameters.

It differs from the candidate `IPRANativeTheory.nativeTheory` in two places:
the candidate takes replacement for *every* formula and steps its induction by
the term `x + 1`. Here replacement for every formula is derived from the atomic
instances by induction on the formula (`leibniz`), and `IPRASuccessorInduction`
and `IPRASuccessorInductionConverse` convert between the two induction forms,
so the two theories prove exactly the same sentences (`provable_iff`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardTheory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ Entailment.FiniteContext
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRAQuantifierFree DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
open DiophantineConsistency.IPRASuccessorInduction DiophantineConsistency.IPRASuccessorInductionConverse
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

/-- Reflexivity, and replacement for atomic formulas with arbitrary parameters. -/
inductive StandardEqualityAxiom : Sentenceᵢ language → Prop
  | refl : StandardEqualityAxiom eqReflI
  | atomic {n k : ℕ} (r : language.Rel k) (ts : Fin k → TermN (n+1)) :
      StandardEqualityAxiom (eqSubstitutionI (Semiformulaᵢ.rel r ts))

inductive StandardAxiom : Sentenceᵢ language → Prop
  | equality {σ} : StandardEqualityAxiom σ → StandardAxiom σ
  | defining {σ} : DefiningEquationI σ → StandardAxiom σ
  | basic {σ} : BasicAxiomI σ → StandardAxiom σ
  | induction {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : OpenI φ →
      StandardAxiom (succInductionAxiom φ)

/-- Standard intuitionistic primitive recursive arithmetic. -/
def standardTheory : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language) := ⟨{σ | StandardAxiom σ}⟩

/-- Monotonicity of `∃` in the Hilbert calculus. -/
def exImplyEx {L : Language} {Λ : Hilbertᵢ L} (A B : Semipropositionᵢ L 1) :
    Λ ⊢! ∀⁰ (A 🡒 B) 🡒 ∃⁰ A 🡒 ∃⁰ B := by
  have hintro : Λ ⊢! free B 🡒 shift (∃⁰ B) := by
    change HilbertProofᵢ Λ (free B 🡒 shift (∃⁰ B))
    simpa using (HilbertProofᵢ.ex₁ (Λ := Λ) (&0) (shift B))
  have hshift : free ((∃⁰ B)/[]) = shift (∃⁰ B) := by
    have hrew : (Rew.free (L := L) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew L ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := ∃⁰ B) hrew
    rw [TransitiveRewriting.comp_app] at he
    exact he
  have hstep : Λ ⊢! ∀⁰ ((A 🡒 B) 🡒 (A 🡒 (∃⁰ B)/[])) := by
    apply HilbertProofᵢ.gen
    have h : Λ ⊢! (free A 🡒 free B) 🡒 (free A 🡒 shift (∃⁰ B)) :=
      Entailment.implyS ⨀ Entailment.C_of_conseq hintro
    simp only [LogicalConnective.HomClass.map_imply, hshift]
    exact h
  exact Entailment.C_trans
    (HilbertProofᵢ.allImplyAllOfAllImply (A 🡒 B) (A 🡒 (∃⁰ B)/[]) ⨀ hstep)
    (HilbertProofᵢ.ex₂ A (∃⁰ B))

/-! ### Replacement for every formula from the atomic instances -/

/-- Moves argument `i` to the front, keeping every argument as a parameter. -/
def sel {m : ℕ} (i : Fin m) : Fin m → TermN (m+1) := fun j => if j = i then #0 else #j.succ

lemma comp_sel {m : ℕ} (i : Fin m) (vars : Fin (m+2) → Term language ℕ) (w : Fin m → Term language ℕ)
    (x : Term language ℕ) (c : Fin (m+1) → TermN (m+2))
    (hc0 : Rew.embSubsts vars (c 0) = x) (hcs : ∀ j : Fin m, Rew.embSubsts vars (c j.succ) = w j)
    (t : TermN m) :
    Rew.embSubsts vars (Rew.subst c (Rew.subst (sel i) t)) = Rew.embSubsts (Function.update w i x) t := by
  have h : ((Rew.embSubsts vars).comp (Rew.subst c)).comp (Rew.subst (sel i)) =
      Rew.embSubsts (Function.update w i x) := by
    ext j
    · by_cases hj : j = i
      · subst hj; simp [Rew.comp_app, sel, hc0]
      · simp [Rew.comp_app, sel, hj, hcs, Function.update_of_ne hj]
    · exact Empty.elim j
  rw [← Rew.comp_app, ← Rew.comp_app, h]

lemma shift_eqAt (u v : Term language ℕ) : shift (eqAt u v) = eqAt (Rew.shift u) (Rew.shift v) := by
  show (Rew.shift ▹ (Semiformulaᵢ.rel Language.ORing.Rel.eq ![u,v] : Propositionᵢ language)) = _
  rw [Semiformulaᵢ.rew_rel]; unfold eqAt; congr 1; funext j; fin_cases j <;> simp

lemma free_q_embSubsts {m : ℕ} (x : Fin m → Term language ℕ) (ψ : Semisentenceᵢ language (m+1)) :
    free ((Rew.embSubsts x).q ▹ ψ) = Rew.embSubsts (&0 :> fun j => Rew.shift (x j)) ▹ ψ := by
  show Rew.free ▹ ((Rew.embSubsts x).q ▹ ψ) = _
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext j
  · cases j using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
  · exact Empty.elim j

lemma cons_shift_update {m : ℕ} (w : Fin m → Term language ℕ) (i : Fin m) (x : Term language ℕ) :
    (&0 :> fun j => Rew.shift (Function.update w i x j)) =
      Function.update (&0 :> fun j => Rew.shift (w j)) i.succ (Rew.shift x) := by
  funext k
  cases k using Fin.cases with
  | zero => rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]; simp
  | succ k =>
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
      simp [Function.update_of_ne hk]

section Replacement
variable {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
  (hrefl : T ⊢! eqReflI)
  (hatom : ∀ {n k : ℕ} (r : language.Rel k) (ts : Fin k → TermN (n+1)),
    T ⊢! eqSubstitutionI (Semiformulaᵢ.rel r ts))

include hatom in
/-- Atomic replacement at an arbitrary argument position. -/
def atomReplace {m k : ℕ} (r : language.Rel k) (ts : Fin k → TermN m) (i : Fin m)
    (w : Fin m → Term language ℕ) (u v : Term language ℕ) :
    extended T ⊢! eqAt u v 🡒 (Rew.embSubsts (Function.update w i u) ▹ Semiformulaᵢ.rel r ts) 🡒
      (Rew.embSubsts (Function.update w i v) ▹ Semiformulaᵢ.rel r ts) := by
  have ha : T ⊢! eqSubstitutionI (Semiformulaᵢ.rel r fun j => Rew.subst (sel i) (ts j)) := hatom r _
  let vars : Fin (m+2) → Term language ℕ := Fin.cases u (Fin.cases v w)
  have hp := instantiateTheory (T := T)
    (leibnizBody (Semiformulaᵢ.rel r fun j => Rew.subst (sel i) (ts j))) ha vars
  have varsOne : vars ((0 : Fin (m+1)).succ) = v := by
    dsimp only [vars]; rw [Fin.cases_succ, Fin.cases_zero]
  have hu := comp_sel i vars w u (Fin.cases #0 (fun j => #j.succ.succ)) (by simp [vars])
    (fun j => by simp [vars])
  have hv := comp_sel i vars w v (Fin.cases #1 (fun j => #j.succ.succ))
    (by simp only [Fin.cases_zero, Rew.embSubsts_bvar]; exact varsOne) (fun j => by simp [vars])
  have he : (fun j : Fin 2 => Rew.embSubsts vars (![#0,#1] j)) = ![u,v] := by
    funext j; cases j using Fin.cases with
    | zero => simp [vars]
    | succ j => cases j using Fin.cases with
      | zero => change vars ((0 : Fin (m+1)).succ) = v; exact varsOne
      | succ j => exact Fin.elim0 j
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    Semiformulaᵢ.rew_rel, hu, hv, he, eqAt] using hp

include hatom in
def eqSymm (u v : Term language ℕ) : extended T ⊢! eqAt u u 🡒 eqAt u v 🡒 eqAt v u := by
  have h := atomReplace hatom (m := 2) (k := 2) Language.ORing.Rel.eq ![#0,#1] 0 ![u,u] u v
  have h1 : (Rew.embSubsts (Function.update ![u,u] 0 u) ▹
      (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#1] : Semisentenceᵢ language 2)) = eqAt u u := by
    rw [Semiformulaᵢ.rew_rel]; unfold eqAt; congr 1; funext j
    fin_cases j <;> simp [Function.update_apply]
  have h2 : (Rew.embSubsts (Function.update ![u,u] 0 v) ▹
      (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#1] : Semisentenceᵢ language 2)) = eqAt v u := by
    rw [Semiformulaᵢ.rew_rel]; unfold eqAt; congr 1; funext j
    fin_cases j <;> simp [Function.update_apply]
  rw [h1, h2] at h
  exact deduct' (deduct (of h ⨀ byAxm₀ ⨀ byAxm₁))

include hrefl in
def eqReflAt (u : Term language ℕ) : extended T ⊢! eqAt u u := by
  have hp := instantiateTheory (T := T)
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#0] : Semisentenceᵢ language 1) hrefl ![u]
  have he : (fun j : Fin 2 => Rew.embSubsts ![u] (![#0,#0] j)) = ![u,u] := by
    funext j; fin_cases j <;> simp
  rw [Semiformulaᵢ.rew_rel, he] at hp
  exact hp

include hrefl hatom in
/-- Replacement at position `i` for every formula. -/
def replace : ∀ {m : ℕ} (φ : Semisentenceᵢ language m) (i : Fin m) (w : Fin m → Term language ℕ)
    (u v : Term language ℕ),
    extended T ⊢! eqAt u v 🡒 (Rew.embSubsts (Function.update w i u) ▹ φ) 🡒
      (Rew.embSubsts (Function.update w i v) ▹ φ)
  | _, ⊥, _, _, _, _ => by
    simpa using (Entailment.C_of_conseq Entailment.C_id :
      extended T ⊢! eqAt _ _ 🡒 ((⊥ : Propositionᵢ language) 🡒 ⊥))
  | _, .rel r ts, i, w, u, v => atomReplace hatom r ts i w u v
  | _, φ ⋏ ψ, i, w, u, v => by
    have h1 := replace φ i w u v
    have h2 := replace ψ i w u v
    simp only [LogicalConnective.HomClass.map_and]
    refine deduct' (deduct ?_)
    exact Entailment.K_intro (of h1 ⨀ byAxm₁ ⨀ Entailment.K_left byAxm₀)
      (of h2 ⨀ byAxm₁ ⨀ Entailment.K_right byAxm₀)
  | _, φ ⋎ ψ, i, w, u, v => by
    have h1 := replace φ i w u v
    have h2 := replace ψ i w u v
    simp only [LogicalConnective.HomClass.map_or]
    refine deduct' ?_
    exact Entailment.or₃ ⨀ Entailment.C_trans (of h1 ⨀ byAxm₀) Entailment.or₁ ⨀
      Entailment.C_trans (of h2 ⨀ byAxm₀) Entailment.or₂
  | _, φ 🡒 ψ, i, w, u, v => by
    have h1 := replace φ i w v u
    have h2 := replace ψ i w u v
    have hs := eqSymm hatom u v
    have hr := eqReflAt hrefl u
    simp only [LogicalConnective.HomClass.map_imply]
    refine deduct' (deduct (deduct ?_))
    exact of h2 ⨀ byAxm₂ ⨀ (byAxm₁ ⨀ (of h1 ⨀ (of hs ⨀ of hr ⨀ byAxm₂) ⨀ byAxm₀))
  | _, ∀⁰ ψ, i, w, u, v => by
    let Au := (Rew.embSubsts (Function.update w i u)).q ▹ ψ
    let Av := (Rew.embSubsts (Function.update w i v)).q ▹ ψ
    have ih := replace ψ i.succ (&0 :> fun j => Rew.shift (w j)) (Rew.shift u) (Rew.shift v)
    have hpoint : extended T ⊢! shift (eqAt u v) 🡒 free (Au 🡒 Av) := by
      simpa only [shift_eqAt, LogicalConnective.HomClass.map_imply, Au, Av, free_q_embSubsts,
        cons_shift_update] using ih
    simpa only [Rewriting.app_all] using
      Entailment.C_trans (HilbertProofᵢ.implyAll hpoint) (HilbertProofᵢ.allImplyAllOfAllImply Au Av)
  | _, ∃⁰ ψ, i, w, u, v => by
    let Au := (Rew.embSubsts (Function.update w i u)).q ▹ ψ
    let Av := (Rew.embSubsts (Function.update w i v)).q ▹ ψ
    have ih := replace ψ i.succ (&0 :> fun j => Rew.shift (w j)) (Rew.shift u) (Rew.shift v)
    have hpoint : extended T ⊢! shift (eqAt u v) 🡒 free (Au 🡒 Av) := by
      simpa only [shift_eqAt, LogicalConnective.HomClass.map_imply, Au, Av, free_q_embSubsts,
        cons_shift_update] using ih
    simpa only [Rewriting.app_exs] using
      Entailment.C_trans (HilbertProofᵢ.implyAll hpoint) (exImplyEx Au Av)

include hrefl hatom in
/-- Full Leibniz replacement, the candidate's equality schema. -/
def leibniz {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : T ⊢! eqSubstitutionI φ := by
  apply closeFamilyT (n+2) (leibnizBody φ)
  intro vars
  let w : Fin (n+1) → Term language ℕ := Fin.cases (vars 0) (fun j => vars j.succ.succ)
  have h := replace hrefl hatom φ 0 w (vars 0) (vars 1)
  have hL : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #0 (fun j => #j.succ.succ))) =
      Rew.embSubsts (Function.update w 0 (vars 0)) := by
    ext j
    · cases j using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => simp [Rew.comp_app, w]
    · exact Empty.elim j
  have hR : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #1 (fun j => #j.succ.succ))) =
      Rew.embSubsts (Function.update w 0 (vars 1)) := by
    ext j
    · cases j using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => simp [Rew.comp_app, w]
    · exact Empty.elim j
  have he : (fun j : Fin 2 => Rew.embSubsts vars (![#0,#1] j)) = ![vars 0, vars 1] := by
    funext j; fin_cases j <;> simp
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    ← TransitiveRewriting.comp_app, hL, hR, Semiformulaᵢ.rew_rel, he, eqAt] using h

end Replacement

/-! ### The two presentations prove the same sentences -/

/-- Provability transfers along a theory whose axioms are all provable. -/
theorem transfer {T U : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (h : ∀ σ ∈ T.theory, U ⊢ σ) {φ : Sentenceᵢ language} (hb : T ⊢ φ) : U ⊢ φ := by
  obtain ⟨b⟩ := hb
  have hp : extended U ⊢! ⋀b.ctx 🡒 Rewriting.emb φ := HilbertProofᵢ.ofLE (le_extended U) b.prf
  have hc : extended U ⊢ ⋀b.ctx := Entailment.Conj₂!_intro (fun ψ hψ => by
    obtain ⟨σ, hσ, rfl⟩ := b.subset ψ hψ
    exact ⟨theoryToExtended U (h σ hσ).some⟩)
  exact ⟨extendedToTheory U (hp ⨀ hc.some)⟩

def ax {σ : Sentenceᵢ language} (h : StandardAxiom σ) : standardTheory ⊢! σ :=
  Axiomatized.prfAxm h

def standardLeibniz {n : ℕ} (φ : Semisentenceᵢ language (n+1)) :
    standardTheory ⊢! eqSubstitutionI φ :=
  leibniz (ax (.equality .refl)) (fun r ts => ax (.equality (.atomic r ts))) φ

theorem standard_equality (σ : Sentenceᵢ language) (h : EqualityAxiomI σ) : standardTheory ⊢ σ := by
  rcases h with _ | φ
  · exact ⟨ax (.equality .refl)⟩
  · exact ⟨standardLeibniz φ⟩

/-- Every axiom of the candidate native theory is a theorem of standard iPRA. -/
theorem native_axiom : ∀ σ ∈ nativeTheory.theory, standardTheory ⊢ σ := by
  intro σ h
  rcases h with h | h | h | h
  · exact standard_equality σ h
  · exact ⟨ax (.defining h)⟩
  · exact ⟨ax (.basic h)⟩
  · obtain ⟨n, φ, hφ, rfl⟩ := h
    exact ⟨plusInductionFromSucc (fun σ h => ax (.defining h))
      (fun σ h => (standard_equality σ h).some) φ (ax (.induction φ hφ))⟩

/-- Every axiom of standard iPRA is a theorem of the candidate native theory. -/
theorem standard_axiom : ∀ σ ∈ standardTheory.theory, nativeTheory ⊢ σ := by
  intro σ h
  rcases h with h | h | h | ⟨φ, hφ⟩
  · rcases h with _ | ⟨r, ts⟩
    · exact ⟨Axiomatized.prfAxm (NativeAxiom.equality .refl)⟩
    · exact ⟨Axiomatized.prfAxm (NativeAxiom.equality (.substitution _))⟩
  · exact ⟨Axiomatized.prfAxm (NativeAxiom.defining h)⟩
  · exact ⟨Axiomatized.prfAxm (NativeAxiom.basic h)⟩
  · exact ⟨successorInduction φ hφ⟩

/-- The candidate native theory and standard iPRA have the same theorems. -/
theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ :=
  ⟨transfer standard_axiom, transfer native_axiom⟩

end DiophantineConsistency.IPRAStandardTheory
