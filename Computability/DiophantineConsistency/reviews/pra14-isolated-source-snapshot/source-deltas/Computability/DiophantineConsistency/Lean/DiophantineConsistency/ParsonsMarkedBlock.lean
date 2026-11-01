import DiophantineConsistency.ParsonsInvariant
import DiophantineConsistency.ParsonsSide
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsMarkedBlock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsInvariant ParsonsBlock ParsonsStructure ParsonsRule ParsonsInductionCase

/-- The actual conclusion of the LK existential rule is the marked block. -/
theorem parameter_root (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    {n : ℕ} (A : ArithmeticSemiformula ℕ (1+n)) (hs : State φ A) :
    (∃⁰ (∃⁰^[n] A)) = (Entry.block φ hφ (1+n) A hs).formula := by
  exact (ParsonsBlock.closure_outer A).symm

/-- The principal existential parameter case in the marked invariant.
The conclusion and premise retain identical side projections. -/
theorem parameter_case (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    {n : ℕ} (A : ArithmeticSemiformula ℕ (1+n)) (hs : State φ A)
    (es : List Entry) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation (((∃⁰^[n] A)/[t]) :: es.map Entry.formula))
    (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Entry.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Entry.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.block φ hφ (1+n) A hs :: es).map Entry.output))) := by
  have heq : ((∃⁰^[n] A)/[t]) :: es.map Entry.formula =
      (Entry.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Entry.formula := by
    simp only [List.map_cons, Entry.formula]
    rw [ParsonsBlock.opening]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.exs.height := by simp [e]
  simpa [Entry.output] using ih e he hh

def baseEntry (ψ : ArithmeticSemiformula ℕ 1) (hψ : Hierarchy 𝚺 1 ψ) : Entry :=
  .side (base ψ) ((ParsonsSide.base_sigma ψ hψ).strict_mono _ (by decide))

def stepEntry (ψ : ArithmeticSemiformula ℕ 1) (hψ : Hierarchy 𝚺 1 ψ) : Entry :=
  .side (step ψ) (ParsonsSide.step_pi_two ψ hψ)

def negativeEntry (ψ : ArithmeticSemiformula ℕ 1) (t : SyntacticTerm ℒₒᵣ)
    (hψ : Hierarchy 𝚺 1 ψ) : Entry :=
  .side (∼(ψ/[t])) ((Hierarchy.neg (Hierarchy.rew (Rew.subst ![t]) hψ)).mono (by decide))

/-- The principal counter-witness case in a marked context, provided that the
remaining projected side disjunction is already Σ₁. -/
theorem counter_case (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (A : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ A))
    (es : List Entry) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation ((A/[t]) :: es.map Entry.formula)) (hc : Derivation.IsCutFree d)
    (hE : Hierarchy 𝚺 1 (disjoin (es.map Entry.output)))
    (ihBase : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((baseEntry ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Entry.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((baseEntry ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Entry.output))))
    (ihStep : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((stepEntry ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Entry.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((stepEntry ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Entry.output))))
    (ihNeg : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((negativeEntry ((Rew.rewrite f).q ▹ φ) t (Hierarchy.rew _ hφ) :: es).map Entry.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((negativeEntry ((Rew.rewrite f).q ▹ φ) t (Hierarchy.rew _ hφ) :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.block φ hφ 0 (∃⁰ A) hs :: es).map Entry.output))) := by
  obtain ⟨f, hf⟩ := ParsonsBlock.finish φ (∃⁰ A) hs
  have hA : A = matrix ((Rew.rewrite f).q ▹ φ) := by simpa using hf
  let ψ : ArithmeticSemiformula ℕ 1 := (Rew.rewrite f).q ▹ φ
  have hψ : Hierarchy 𝚺 1 ψ := Hierarchy.rew _ hφ
  have deq : (A/[t]) :: es.map Entry.formula = (matrix ψ)/[t] :: es.map Entry.formula := by
    rw [hA]
  let d' := d.cast deq
  have hc' : Derivation.IsCutFree d' := by simpa [d'] using hc
  have hheight : d'.exs.height = d.exs.height := by simp [d']
  have hresult : Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output))) :=
    one_case ψ (disjoin (es.map Entry.output)) t (es.map Entry.formula) d' hc' hψ hE
      (by
        intro e he hh
        have hr := ihBase f hA e he (by rw [← hheight]; exact hh)
        simpa [baseEntry, Entry.output, disjoin] using hr)
      (by
        intro e he hh
        have hr := ihStep f hA e he (by rw [← hheight]; exact hh)
        simpa [stepEntry, Entry.output, disjoin] using hr)
      (by
        intro e he hh
        have hr := ihNeg f hA e he (by rw [← hheight]; exact hh)
        simpa [negativeEntry, Entry.output, disjoin] using hr)
  have hw : Proof 𝗣𝗔⁻ ((disjoin (es.map Entry.output)) 🡒 (⊥ ⋎ disjoin (es.map Entry.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simp [hf])
  simpa [Entry.output, disjoin] using Nonempty.intro (Proof.mp hw hresult.some)

end DiophantineConsistency.ParsonsMarkedBlock
