import DiophantineConsistency.ParsonsGuardedCollection
import DiophantineConsistency.ParsonsPrenexAll
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsLogicalCases
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsGuard ParsonsGuardedCollection

def existential_lk (A : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) :
    Derivation [((A/[t]) ⋎ E) 🡒 (∃⁰ guard A E)] := by
  let X := (A/[t]) ⋎ E
  have h : Derivation [(guard A E)/[t], ∼X] := by
    simpa [X] using Derivation.close X (Δ := [X, ∼X]) (by simp) (by simp)
  have he := h.exs
  simpa [X, Semiformula.imp_eq] using (he.contra (Γ := [∼X, ∃⁰ guard A E]) (by simp)).or

def existential (A : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) (h : Proof 𝗣𝗔⁻ ((A/[t]) ⋎ E)) :
    Proof 𝗣𝗔⁻ (E ⋎ (∃⁰ A)) := by
  exact ParsonsPrenex.prove_exs_to_disjunction A E (.mp (.logical (existential_lk A E t)) h)

def universal (A : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (h : Proof 𝗣𝗔⁻ (A.free ⋎ Rewriting.shift E)) : Proof 𝗣𝗔⁻ (E ⋎ (∀⁰ A)) := by
  have hfree : (guard A E).free = A.free ⋎ Rewriting.shift E := by
    simp [ParsonsGuard.guard, ← TransitiveRewriting.comp_app]
  have hg : Proof 𝗣𝗔⁻ (guard A E).free := by simpa [hfree] using h
  exact ParsonsPrenexAll.prove_all_to_disjunction A E (.generalize hg)

noncomputable def disjunction (P Q E : Proposition ℒₒᵣ)
    (h : Proof 𝗣𝗔⁻ (P ⋎ (Q ⋎ E))) : Proof 𝗣𝗔⁻ ((P ⋎ Q) ⋎ E) := by
  have hp : Proof 𝗣𝗔⁻ ((P ⋎ (Q ⋎ E)) 🡒 ((P ⋎ Q) ⋎ E)) := of_semantics _ _ (by
    intro M _ _ f
    simp
    tauto)
  exact .mp hp h

noncomputable def conjunction (P Q E : Proposition ℒₒᵣ)
    (hp : Proof 𝗣𝗔⁻ (P ⋎ E)) (hq : Proof 𝗣𝗔⁻ (Q ⋎ E)) :
    Proof 𝗣𝗔⁻ ((P ⋏ Q) ⋎ E) := by
  have h : Proof 𝗣𝗔⁻ ((P ⋎ E) 🡒 ((Q ⋎ E) 🡒 ((P ⋏ Q) ⋎ E))) := of_semantics _ _ (by
    intro M _ _ f
    simp [Semiformula.imp_eq]
    tauto)
  exact .mp (.mp h hp) hq

/-- Principal existential side case, with the recursive result supplied only
for genuinely smaller cut-free premises. -/
theorem existential_case (A : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) (Γ : Sequent ℒₒᵣ)
    (d : Derivation ((A/[t]) :: Γ)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((A/[t]) :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (Proof 𝗣𝗔⁻ ((A/[t]) ⋎ E))) :
    Nonempty (Proof 𝗣𝗔⁻ (E ⋎ (∃⁰ A))) := by
  have hh : d.height < d.exs.height := by simp
  exact ⟨existential A E t (ih d hc hh).some⟩

theorem universal_case (A : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (Γ : Sequent ℒₒᵣ) (d : Derivation (A.free :: Γ⁺)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation (A.free :: Γ⁺), Derivation.IsCutFree e →
      e.height < d.all.height → Nonempty (Proof 𝗣𝗔⁻ (A.free ⋎ Rewriting.shift E))) :
    Nonempty (Proof 𝗣𝗔⁻ (E ⋎ (∀⁰ A))) := by
  have hh : d.height < d.all.height := by simp
  exact ⟨universal A E (ih d hc hh).some⟩

theorem disjunction_case (P Q E : Proposition ℒₒᵣ) (Γ : Sequent ℒₒᵣ)
    (d : Derivation (P :: Q :: Γ)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation (P :: Q :: Γ), Derivation.IsCutFree e →
      e.height < d.or.height → Nonempty (Proof 𝗣𝗔⁻ (P ⋎ (Q ⋎ E)))) :
    Nonempty (Proof 𝗣𝗔⁻ ((P ⋎ Q) ⋎ E)) := by
  have hh : d.height < d.or.height := by simp
  exact ⟨disjunction P Q E (ih d hc hh).some⟩

theorem conjunction_case (P Q E : Proposition ℒₒᵣ) (Γ : Sequent ℒₒᵣ)
    (dP : Derivation (P :: Γ)) (dQ : Derivation (Q :: Γ))
    (hcP : Derivation.IsCutFree dP) (hcQ : Derivation.IsCutFree dQ)
    (ihP : ∀ e : Derivation (P :: Γ), Derivation.IsCutFree e →
      e.height < (dP.and dQ).height → Nonempty (Proof 𝗣𝗔⁻ (P ⋎ E)))
    (ihQ : ∀ e : Derivation (Q :: Γ), Derivation.IsCutFree e →
      e.height < (dP.and dQ).height → Nonempty (Proof 𝗣𝗔⁻ (Q ⋎ E))) :
    Nonempty (Proof 𝗣𝗔⁻ ((P ⋏ Q) ⋎ E)) := by
  have hp : dP.height < (dP.and dQ).height := by simp
  have hq : dQ.height < (dP.and dQ).height := by simp
  exact ⟨conjunction P Q E (ihP dP hcP hp).some (ihQ dQ hcQ hq).some⟩

end DiophantineConsistency.ParsonsLogicalCases
