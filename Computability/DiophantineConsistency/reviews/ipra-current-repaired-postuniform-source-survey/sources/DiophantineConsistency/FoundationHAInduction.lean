import Foundation.FirstOrder.Arithmetic.Schemata
import DiophantineConsistency.FoundationHAEquality
import DiophantineConsistency.FoundationHAClosure

/-! # Arbitrary Foundation induction instances in conventional HA

The exact source `succInd` and its parameter closure are used. The target
applies HA's actual formula-induction schema to the translated body. The
source step `x+1` is replaced by `S x` using a proved HA equality inside an
arbitrary formula; it is not a definitional identification of syntax.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAInduction
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAEquality FoundationHAClosure
open SetTheory.PA HA

/-- Replace slot zero while retaining every ambient slot. -/
def replaceZero (t : Term) : Nat → Term
  | 0 => t
  | n+1 => .var (n+1)

def addOneSubst : Nat → Term := replaceZero (.add (.var 0) (.succ .zero))

theorem hole_substitution (a : Formula) (t : Term) :
    Formula.subst (Formula.instTerm t) (Formula.rename (SetTheory.up Nat.succ) a) =
      Formula.subst (replaceZero t) a := by
  rw [Formula.subst_rename]
  apply Formula.subst_ext
  intro n
  cases n <;> rfl

theorem successor_substitution : replaceZero (.succ (.var 0)) = Formula.substSuccVar := by
  funext n
  cases n <;> rfl

/-- Genuine Leibniz transport under any formula, including nested binders.
Only the one-hole formula's ambient variables are shifted. -/
theorem add_one_replacement {G : List Formula} (a : Formula)
    (h : Relative Formula.Ax_s G (Formula.subst addOneSubst a)) :
    Relative Formula.Ax_s G (Formula.subst Formula.substSuccVar a) := by
  have h₀ : Relative Formula.Ax_s G (Formula.subst
      (Formula.instTerm (.add (.var 0) (.succ .zero)))
      (Formula.rename (SetTheory.up Nat.succ) a)) := by
    simpa only [hole_substitution, addOneSubst] using h
  have he : Relative Formula.Ax_s G
      (.eq (.add (.var 0) (.succ .zero)) (.succ (.var 0))) :=
    (Arithmetic.add_one (.var 0)).weaken (by simp)
  have h₁ := Relative.eq_elim (Formula.rename (SetTheory.up Nat.succ) a) he h₀
  simpa only [hole_substitution, successor_substitution] using h₁

/-- Substitution at the single source bound variable retains source free
parameters in target slots 1,2,... when the target still has one binder. -/
theorem formula_subst_same (ψ : Semiformulaᵢ ℒₒᵣ Nat 1)
    (t : SyntacticSemiterm ℒₒᵣ 1) :
    formula (ψ ⇜ (fun _ => t)) = Formula.subst (replaceZero (term t)) (formula ψ) := by
  unfold formula
  rw [formulaAux_rew, formulaAux_subst]
  congr 1
  · funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  · funext j
    simp only [Rew.subst_fvar, termAux, Term.subst]
    rw [Nat.add_comm 1 j]
    rfl

private def sourceZero : SyntacticTerm ℒₒᵣ := ‘0’
private def sourceAddOne : SyntacticSemiterm ℒₒᵣ 1 := ‘#0 + 1’

/-- Zero removes the source's unique bound slot and lowers all parameter slots. -/
theorem translated_zero (φ : Semiformula ℒₒᵣ Nat 1) :
    formula (φ ⇜ (fun _ => sourceZero))ᴺ =
      Formula.subst Formula.substZero (formula φᴺ) := by
  rw [← Semiformula.subst_doubleNegation, formula_inst, Formula.substZero_eq_instTerm]
  rfl

/-- The source successor step keeps parameter slots fixed. -/
theorem translated_add_one (φ : Semiformula ℒₒᵣ Nat 1) :
    formula (φ ⇜ (fun _ => sourceAddOne))ᴺ =
      Formula.subst addOneSubst (formula φᴺ) := by
  rw [← Semiformula.subst_doubleNegation, formula_subst_same]
  rfl

/-- Open the single source binder after GG; the canonical target slots agree. -/
theorem translated_free (φ : Semiformula ℒₒᵣ Nat 1) :
    formula (Rewriting.free φ)ᴺ = formula φᴺ := by
  rw [← Semiformula.rew_doubleNegation]
  exact formula_free φᴺ

/-- The source universal notation and GG commute before target interpretation. -/
theorem translated_all (φ : Semiformula ℒₒᵣ Nat 1) :
    formula (∀⁰ φ)ᴺ = Formula.all (formula φᴺ) := by
  rw [Semiformula.doubleNegation_all]
  exact formula_all φᴺ

/-- The reverse implication conversion uses the existing Foundation theorem,
with every finite target assumption retained. -/
theorem translated_imp_elim {G : List Formula} (φ ψ : Proposition ℒₒᵣ)
    (h : Relative Formula.Ax_s G (formula (φ 🡒 ψ)ᴺ)) :
    Relative Formula.Ax_s G (.imp (formula φᴺ) (formula ψᴺ)) := by
  obtain ⟨p⟩ := (LO.FirstOrder.Derivation.imply_doubleNegation
    (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)) φ ψ)
  have hi := FoundationPAHFLogic.intuitionistic_proof p
  change Derives [] (.and
    (.imp (.imp (formula φᴺ) (formula ψᴺ)) (formula (φ 🡒 ψ)ᴺ))
    (.imp (formula (φ 🡒 ψ)ᴺ) (.imp (formula φᴺ) (formula ψᴺ)))) at hi
  exact ((relative_of_derives hi).and_right.weaken (by simp)).mp h

private theorem translated_imp_elim_one {G : List Formula}
    (φ ψ : Semiformula ℒₒᵣ Nat 1)
    (h : Relative Formula.Ax_s G (formula (φ 🡒 ψ)ᴺ)) :
    Relative Formula.Ax_s G (.imp (formula φᴺ) (formula ψᴺ)) := by
  have h' : Relative Formula.Ax_s G
      (formula ((Rewriting.free φ) 🡒 (Rewriting.free ψ))ᴺ) := by
    rw [← LogicalConnective.HomClass.map_imply, translated_free]
    exact h
  have hi := translated_imp_elim (Rewriting.free φ) (Rewriting.free ψ) h'
  simpa only [translated_free] using hi

private theorem open_shifted_all {G : List Formula} {a : Formula}
    (h : Relative Formula.Ax_s G (Formula.rename Nat.succ (.all a))) :
    Relative Formula.Ax_s G a := by
  have hi := Relative.all_elim (.var 0) h
  simpa only [Formula.rename, Formula.subst_instTerm_var_zero_rename_up_succ] using hi

/-- The existing source definition, with its curried premises and no model
hypotheses. The identity one-variable substitutions are simplified only. -/
theorem source_succInd (φ : Semiformula ℒₒᵣ Nat 1) :
    LO.FirstOrder.Arithmetic.succInd φ =
      ((φ ⇜ (fun _ => sourceZero)) 🡒
        ((∀⁰ (φ 🡒 (φ ⇜ (fun _ => sourceAddOne)))) 🡒 ∀⁰ φ)) := by
  unfold LO.FirstOrder.Arithmetic.succInd
  simp [sourceZero, sourceAddOne, Matrix.constant_eq_singleton]

/-- Actual HA formula induction on the translated arbitrary body. No source
axiom-image, semantic induction, or restricted-fragment premise is supplied. -/
theorem succInd_open (φ : Semiformula ℒₒᵣ Nat 1) :
    Proves (formula (LO.FirstOrder.Arithmetic.succInd φ)ᴺ) := by
  rw [source_succInd]
  apply translated_imp
  apply Relative.imp_intro
  apply translated_imp
  apply Relative.imp_intro
  simp only [translated_all]
  apply Arithmetic.induction (formula φᴺ)
  · rw [← translated_zero]
    exact Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  · apply Relative.all_intro Formula.Ax_s_sentences
    apply Relative.imp_intro
    have hstep : Relative Formula.Ax_s
        ((formula φᴺ) ::
          [formula (∀⁰ (φ 🡒 (φ ⇜ (fun _ => sourceAddOne))))ᴺ,
           formula (φ ⇜ (fun _ => sourceZero))ᴺ].map (Formula.rename Nat.succ))
        (Formula.rename Nat.succ
          (formula (∀⁰ (φ 🡒 (φ ⇜ (fun _ => sourceAddOne))))ᴺ)) := by
      apply Relative.hypothesis
      simp only [List.map_cons, List.map_nil, List.mem_cons]
      exact Or.inr (Or.inl True.intro)
    have hs := hstep
    simp only [translated_all] at hs
    have hp := (translated_imp_elim_one φ _ (open_shifted_all hs)).mp
      (Relative.hypothesis List.mem_cons_self)
    apply add_one_replacement
    rw [← translated_add_one φ]
    exact hp

/-- The actual source parameter closure, not an independently chosen closure. -/
theorem succInd_closed (φ : Semiformula ℒₒᵣ Nat 1) :
    Proves (sentence (Semiformula.univCl (LO.FirstOrder.Arithmetic.succInd φ))ᴺ) :=
  proves_univCl _ (succInd_open φ)

/-- Every member of Foundation's unrestricted first-order induction schema
has its literal GG image proved in conventional HA. -/
theorem induction_axiom {σ : Sentence ℒₒᵣ}
    (h : σ ∈ LO.FirstOrder.Arithmetic.InductionScheme ℒₒᵣ Set.univ) :
    Proves (sentence σᴺ) := by
  obtain ⟨φ, _, rfl⟩ := h
  exact succInd_closed φ

end DiophantineConsistency.FoundationHAInduction
