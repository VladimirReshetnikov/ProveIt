import DiophantineConsistency.ParsonsInvariant
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBaseState
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsInvariant ParsonsStructure

/-- A positive theorem whose negation is being processed in a sequent.
Rewritten proofs are stored explicitly so eigenvariable shifts remain valid. -/
structure BaseState where
  positive : Proposition ℒₒᵣ
  piTwo : Hierarchy 𝚷 2 positive
  rewritten : ∀ f : ℕ → SyntacticTerm ℒₒᵣ, Proof 𝗣𝗔⁻ (Rew.rewrite f ▹ positive)

def BaseState.negative (s : BaseState) : Proposition ℒₒᵣ := ∼s.positive

/-- Any PA-minus axiom with its Π₂ certificate initializes such a state. -/
def ofAxiom (σ : ArithmeticSentence) (hσ : σ ∈ 𝗣𝗔⁻)
    (hPi : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) : BaseState where
  positive := Rewriting.emb σ
  piTwo := hPi
  rewritten := fun f => by simpa using (Proof.axiom hσ)

/-- A universal theorem remains a theorem after arbitrary witness
specialization, uniformly under all future free-variable rewrites. -/
def openUniversal (A : ArithmeticSemiformula ℕ 1)
    (hPi : Hierarchy 𝚷 2 (∀⁰ A))
    (h : ∀ f : ℕ → SyntacticTerm ℒₒᵣ, Proof 𝗣𝗔⁻ (Rew.rewrite f ▹ (∀⁰ A)))
    (t : SyntacticTerm ℒₒᵣ) : BaseState where
  positive := A/[t]
  piTwo := Hierarchy.rew (Rew.subst ![t]) (Hierarchy.pi_of_pi_all hPi)
  rewritten := fun f => by
    have hu : Proof 𝗣𝗔⁻ (∀⁰ (Rew.rewrite (Rew.bShift ∘ f) ▹ A)) := by simpa [Rew.q_rewrite] using h f
    have ht := Proof.specialize (Rew.rewrite f t) hu
    simpa [LawfulSyntacticRewriting.rewrite_subst_eq] using ht

/-- The existential witness premise of the negative universal is exactly
negative the specialized theorem. -/
theorem negative_instance (A : ArithmeticSemiformula ℕ 1)
    (hPi : Hierarchy 𝚷 2 (∀⁰ A))
    (h : ∀ f : ℕ → SyntacticTerm ℒₒᵣ, Proof 𝗣𝗔⁻ (Rew.rewrite f ▹ (∀⁰ A)))
    (t : SyntacticTerm ℒₒᵣ) :
    (∼A)/[t] = (openUniversal A hPi h t).negative := by simp [openUniversal, BaseState.negative]

/-- Apply the universal transition to an existing base state. -/
def openState (s : BaseState) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) : BaseState :=
  openUniversal A (by rw [← hEq]; exact s.piTwo)
    (fun f => by rw [← hEq]; exact s.rewritten f) t

/-- Eigenvariable shifts preserve both the Π₂ classification and the full
family of rewritten theorem proofs. -/
def shiftState (s : BaseState) : BaseState where
  positive := Rewriting.shift s.positive
  piTwo := Hierarchy.rew Rew.shift s.piTwo
  rewritten := fun f => by
    have he : (Rew.rewrite f).comp Rew.shift = Rew.rewrite (fun i => f (i+1)) := by
      ext i <;> simp [Rew.comp_app]
    have hp := s.rewritten (fun i => f (i+1))
    simpa [← TransitiveRewriting.comp_app, he] using hp

/-- Once the positive theorem is Σ₁, its negation is a valid Π₂ side entry. -/
def terminal (s : BaseState) (hSig : Hierarchy 𝚺 1 s.positive) : Entry :=
  .side s.negative ((Hierarchy.neg hSig).strict_mono _ (by decide))

def BaseState.proof (s : BaseState) : Proof 𝗣𝗔⁻ s.positive := by
  have h := s.rewritten (fun i => &i)
  simpa using h

/-- Discharge the terminal negative theorem from a side disjunction. -/
noncomputable def discharge (s : BaseState) (E : Proposition ℒₒᵣ)
    (h : Proof 𝗣𝗔⁻ (s.negative ⋎ E)) : Proof 𝗣𝗔⁻ E := by
  have hp : Proof 𝗣𝗔⁻ (s.positive ⋎ E) := by
    have hi : Proof 𝗣𝗔⁻ (s.positive 🡒 (s.positive ⋎ E)) :=
      ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hp; simp [hp])
    exact .mp hi s.proof
  exact .mp (.mp (.logical (resolution s.positive E)) hp) h

/-- The principal existential case of a negative universal base state. -/
theorem open_case (s : BaseState) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) (es : List Entry)
    (d : Derivation (((∼A)/[t]) :: es.map Entry.formula)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((openState s A hEq t).negative :: es.map Entry.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output))) := by
  have heq : ((∼A)/[t]) :: es.map Entry.formula =
      (openState s A hEq t).negative :: es.map Entry.formula := by
    simp [openState, openUniversal, BaseState.negative]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.exs.height := by simp [e]
  exact ih e he hh

/-- At the terminal Σ₁ positive instance, reclassification as a Π₂ side
followed by resolution removes that side from the output. This does not
reduce derivation height; a global induction must use a secondary measure. -/
theorem terminal_case (s : BaseState) (hSig : Hierarchy 𝚺 1 s.positive)
    (es : List Entry)
    (h : Nonempty (Proof 𝗣𝗔⁻ (disjoin ((terminal s hSig :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output))) := by
  have hp : Proof 𝗣𝗔⁻ (s.negative ⋎ disjoin (es.map Entry.output)) := by
    simpa [terminal, Entry.output, disjoin] using h.some
  exact ⟨discharge s _ hp⟩

end DiophantineConsistency.ParsonsBaseState
