import DiophantineConsistency.ParsonsBaseShape
import DiophantineConsistency.ParsonsShift
import DiophantineConsistency.ParsonsFold
import DiophantineConsistency.ParsonsMarkedLogical
import DiophantineConsistency.ParsonsMarkedBlock
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsUnified
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsStructure ParsonsBlock ParsonsOpened ParsonsBaseShape ParsonsLogicalCases ParsonsInductionCase

/-- A fully tracked sequent occurrence: Π₂ side, shaped positive base theorem
represented negatively, or partially opened Σ₁ induction block. -/
inductive Mark where
  | side (P : Proposition ℒₒᵣ) (hP : Hierarchy 𝚷 2 P)
  | base (s : ShapedBase)
  | block (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
      (n : ℕ) (A : ArithmeticSemiformula ℕ n) (h : State φ A)

def Mark.formula : Mark → Proposition ℒₒᵣ
  | .side P _ => P
  | .base s => s.state.negative
  | .block _ _ _ A _ => ∃⁰* A

def Mark.output : Mark → Proposition ℒₒᵣ
  | .side P _ => P
  | .base _ => ⊥
  | .block _ _ _ _ _ => ⊥

def Mark.isBlock : Mark → Prop
  | .block _ _ _ _ _ => True
  | _ => False

def Mark.fromEntry : ParsonsInvariant.Entry → Mark
  | .side P hP => .side P hP
  | .base σ hσ => .base (ParsonsBaseShape.initial σ hσ)
  | .block φ hφ n A hs => .block φ hφ n A hs

theorem fromEntry_formula (e : ParsonsInvariant.Entry) :
    (Mark.fromEntry e).formula = e.formula := by
  cases e <;> simp [Mark.fromEntry, Mark.formula, ParsonsInvariant.Entry.formula,
    ParsonsBaseShape.initial, ParsonsBaseState.ofAxiom, ParsonsBaseState.BaseState.negative]

theorem fromEntry_output (e : ParsonsInvariant.Entry) :
    (Mark.fromEntry e).output = e.output := by
  cases e <;> simp [Mark.fromEntry, Mark.output, ParsonsInvariant.Entry.output]

def initial {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) : List Mark :=
  (ParsonsInvariant.initial p hσ).map Mark.fromEntry

theorem initial_formula {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) :
    (initial p hσ).map Mark.formula = (ParsonsInvariant.initial p hσ).map ParsonsInvariant.Entry.formula := by
  simp [initial, List.map_map, Function.comp_def, fromEntry_formula]

def initial_derivation {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) :
    {d : Derivation ((initial p hσ).map Mark.formula) // Derivation.IsCutFree d} := by
  rw [initial_formula]
  exact ParsonsInvariant.initial_derivation p hσ

noncomputable def initial_result {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ))
    (h : Proof 𝗣𝗔⁻ (disjoin ((initial p hσ).map Mark.output))) : Proof 𝗣𝗔⁻ (Rewriting.emb σ) := by
  apply ParsonsInvariant.initial_result p hσ
  simpa [initial, List.map_map, Function.comp_def, fromEntry_output] using h

/-- Shift all marked occurrences across an eigenvariable introduction. -/
def Mark.shift : Mark → Mark
  | .side P hP => .side (Rewriting.shift P) (Hierarchy.rew Rew.shift hP)
  | .base s => .base (ParsonsBaseShape.shiftState s)
  | .block φ hφ n A hs => .block φ hφ n (Rew.shift ▹ A) (ParsonsShift.state_shift φ A hs)

theorem shift_formula (e : Mark) : (Mark.shift e).formula = Rewriting.shift e.formula := by
  cases e with
  | side P h => rfl
  | base s => simp [Mark.shift, Mark.formula, ParsonsBaseShape.shiftState,
      ParsonsBaseState.shiftState, ParsonsBaseState.BaseState.negative]
  | block φ hφ n A hs => simp [Mark.shift, Mark.formula, ParsonsShift.shift_closure]

theorem shift_output (e : Mark) : (Mark.shift e).output = Rewriting.shift e.output := by
  cases e <;> simp [Mark.shift, Mark.output]

theorem output_pi_two (es : List Mark) : Hierarchy 𝚷 2 (disjoin (es.map Mark.output)) := by
  induction es with
  | nil => simp [disjoin]
  | cons e es ih =>
    cases e with
    | side P hP => simpa [disjoin, Mark.output] using And.intro hP ih
    | base s => simpa [disjoin, Mark.output] using ih
    | block φ hφ n A hs => simpa [disjoin, Mark.output] using ih

def weight : Mark → ℕ
  | .base _ => 1
  | _ => 0

def baseCount (es : List Mark) : ℕ := (es.map weight).sum

/-- The terminal base reclassification leaves derivation height unchanged but
strictly reduces the secondary count of marked base states. -/
theorem terminal_measure (s : ShapedBase) (hSig : Hierarchy 𝚺 1 s.state.positive)
    (es : List Mark) :
    baseCount (Mark.side s.state.negative ((Hierarchy.neg hSig).strict_mono _ (by decide)) :: es) <
      baseCount (Mark.base s :: es) := by
  simp [baseCount, weight]

/-- Principal negative-universal transition in the unified context. -/
theorem base_open (s : ShapedBase) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.state.positive = ∀⁰ A) (t : SyntacticTerm ℒₒᵣ) (es : List Mark)
    (d : Derivation (((∼A)/[t]) :: es.map Mark.formula)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Mark.base (ParsonsBaseShape.openState s A hEq t) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.base (ParsonsBaseShape.openState s A hEq t) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.base s :: es).map Mark.output))) := by
  have heq : ((∼A)/[t]) :: es.map Mark.formula =
      (Mark.base (ParsonsBaseShape.openState s A hEq t) :: es).map Mark.formula := by
    simp [Mark.formula, ParsonsBaseShape.openState, ParsonsBaseState.openState,
      ParsonsBaseState.openUniversal, ParsonsBaseState.BaseState.negative]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.exs.height := by simp [e]
  simpa [Mark.output] using ih e he hh

/-- Same-height terminal reclassification of a base state. -/
theorem base_terminal (s : ShapedBase) (hSig : Hierarchy 𝚺 1 s.state.positive)
    (es : List Mark)
    (h : Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side s.state.negative
      ((Hierarchy.neg hSig).strict_mono _ (by decide)) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.base s :: es).map Mark.output))) := by
  have hp : Proof 𝗣𝗔⁻ (s.state.negative ⋎ disjoin (es.map Mark.output)) := by
    simpa [Mark.output, disjoin] using h.some
  have he := ParsonsBaseState.discharge s.state _ hp
  have hw : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output)) 🡒 (⊥ ⋎ disjoin (es.map Mark.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simp [hf])
  simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hw he)

def ordinary : List Mark → List (Proposition ℒₒᵣ)
  | [] => []
  | .side P _ :: es => P :: ordinary es
  | _ :: es => ordinary es

def bases : List Mark → List ShapedBase
  | [] => []
  | .base s :: es => s :: bases es
  | _ :: es => bases es

theorem ordinary_subset_output (es : List Mark) : ordinary es ⊆ es.map Mark.output := by
  induction es with
  | nil => simp [ordinary]
  | cons e es ih =>
    cases e with
    | side P hP =>
      intro Q hQ
      simp only [ordinary, List.mem_cons] at hQ
      rcases hQ with rfl | hQ
      · simp [Mark.output]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih hQ)
    | base s =>
      intro Q hQ
      simp only [ordinary] at hQ
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih hQ)
    | block φ hφ n A hs =>
      intro Q hQ
      simp only [ordinary] at hQ
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih hQ)

theorem plain_subset_base (es : List Mark)
    (hn : ∀ e ∈ es, ¬e.isBlock) :
    es.map Mark.formula ⊆ ordinary es ++ (bases es).map (fun s => s.state.negative) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have htail : ∀ e ∈ es, ¬e.isBlock := by intro x hx; exact hn x (by simp [hx])
    have ht := ih htail
    intro P hp
    simp only [List.map_cons, List.mem_cons] at hp
    rcases hp with hp | hp
    · subst P
      cases e with
      | side Q hQ => simp [ordinary, Mark.formula]
      | base s => simp [ordinary, bases, Mark.formula]
      | block φ hφ n A hs =>
        have hb := hn (Mark.block φ hφ n A hs) (by simp)
        simp [Mark.isBlock] at hb
    · have hm := ht hp
      cases e with
      | side Q hQ =>
        simp only [ordinary, bases, List.cons_append, List.mem_cons]
        exact Or.inr hm
      | base s =>
        simp only [ordinary, bases, List.map_cons, List.mem_append, List.mem_cons] at hm ⊢
        tauto
      | block φ hφ n A hs =>
        have hb := hn (Mark.block φ hφ n A hs) (by simp)
        simp [Mark.isBlock] at hb

/-- When no induction block remains, arbitrary interleaved shaped base
states are discharged using their actual stored proofs. -/
noncomputable def base_branch (es : List Mark)
    (hn : ∀ e ∈ es, ¬e.isBlock) (d : Derivation (es.map Mark.formula)) :
    Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output)) := by
  let B : List (Proposition ℒₒᵣ) := (bases es).map (fun s => s.state.positive)
  have hs := plain_subset_base es hn
  have hd0 : Derivation (ordinary es ++ (bases es).map (fun s => s.state.negative)) := d.contra hs
  have hd : Derivation (disjoin (ordinary es) :: ∼B) := by
    simpa [B, ParsonsBaseState.BaseState.negative, List.tilde_def, List.map_map, Function.comp_def] using
      ParsonsFold.fold_context (ordinary es) ((bases es).map (fun s => s.state.negative)) hd0
  have hp : ∀ P ∈ B, Proof 𝗣𝗔⁻ P := by
    intro P hP
    let s := Classical.choose (List.mem_map.mp hP)
    have hh := Classical.choose_spec (List.mem_map.mp hP)
    exact hh.2 ▸ s.state.proof
  have he := ParsonsRuleEmbedding.fromContext B hp (disjoin (ordinary es)) hd
  exact weakening (ordinary es) (es.map Mark.output) (ordinary_subset_output es) he

/-- Select a marked occurrence for each formula in a premise sub-sequent.
Different occurrences of the same formula may have different roles. -/
noncomputable def selectEntries (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) : List Mark :=
  Δ.attach.map (fun x => Classical.choose (List.mem_map.mp (hsub x.property)))

theorem selected_subset (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) : selectEntries Δ es hsub ⊆ es := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact (Classical.choose_spec (List.mem_map.mp (hsub x.property))).1

theorem selected_formulas (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) :
    (selectEntries Δ es hsub).map Mark.formula = Δ := by
  simp only [selectEntries, List.map_map, Function.comp_def]
  rw [show (fun x : {P // P ∈ Δ} => Mark.formula
      (Classical.choose (List.mem_map.mp (hsub x.property)))) = Subtype.val by
    funext x
    exact (Classical.choose_spec (List.mem_map.mp (hsub x.property))).2]
  exact List.attach_map_subtype_val Δ

theorem selected_outputs_subset (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) :
    (selectEntries Δ es hsub).map Mark.output ⊆ es.map Mark.output := by
  intro P hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨e, selected_subset Δ es hsub he, rfl⟩

/-- Contraction for marked contexts, preserving the chosen role of each
premise occurrence and invoking a strictly smaller cut-free derivation. -/
theorem marked_contraction (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) (d : Derivation Δ) (hc : Derivation.IsCutFree d)
    (ih : ∀ (e : Derivation Δ), Derivation.IsCutFree e →
      e.height < (d.contraction hsub).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((selectEntries Δ es hsub).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output))) := by
  have hh : d.height < (d.contraction hsub).height := by simp
  exact ⟨weakening _ _ (selected_outputs_subset Δ es hsub) (ih d hc hh).some⟩

theorem shift_formulas (es : List Mark) :
    (es.map Mark.shift).map Mark.formula = (es.map Mark.formula)⁺ := by
  simp [Rewriting.shifts, List.map_map, Function.comp_def, shift_formula]

theorem shift_outputs (es : List Mark) :
    (es.map Mark.shift).map Mark.output = (es.map Mark.output)⁺ := by
  simp [Rewriting.shifts, List.map_map, Function.comp_def, shift_output]

theorem base_root (s : ShapedBase) (A : ArithmeticSemiformula ℕ 1)
    (hEq : s.state.positive = ∀⁰ A) : s.state.negative = ∃⁰ ∼A := by
  simp [ParsonsBaseState.BaseState.negative, hEq]

theorem terminal_formula (s : ShapedBase) (hSig : Hierarchy 𝚺 1 s.state.positive) :
    (Mark.side s.state.negative ((Hierarchy.neg hSig).strict_mono _ (by decide))).formula =
      (Mark.base s).formula := rfl

/-- Opening a Π₂ universal preserves Π₂ classification at the eigenvariable. -/
theorem opened_pi_two (A : ArithmeticSemiformula ℕ 1)
    (hA : Hierarchy 𝚷 2 (∀⁰ A)) : Hierarchy 𝚷 2 A.free :=
  Hierarchy.rew Rew.free (Hierarchy.pi_of_pi_all hA)

/-- The ordinary universal rule with an arbitrary marked nonprincipal
context. Every entry, including partially opened induction blocks, is shifted
coherently before invoking the strictly smaller premise. -/
theorem marked_universal (A : ArithmeticSemiformula ℕ 1)
    (hA : Hierarchy 𝚷 2 (∀⁰ A)) (es : List Mark)
    (d : Derivation (A.free :: (es.map Mark.formula)⁺)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Mark.side A.free (opened_pi_two A hA) :: es.map Mark.shift).map Mark.formula),
      Derivation.IsCutFree e → e.height < d.all.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side A.free (opened_pi_two A hA) :: es.map Mark.shift).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side (∀⁰ A) hA :: es).map Mark.output))) := by
  have heq : A.free :: (es.map Mark.formula)⁺ =
      (Mark.side A.free (opened_pi_two A hA) :: es.map Mark.shift).map Mark.formula := by
    simp only [List.map_cons, Mark.formula]
    rw [shift_formulas]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.all.height := by simp [e]
  have hp : Proof 𝗣𝗔⁻ (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output))) := by
    simpa only [List.map_cons, Mark.output, disjoin, shift_outputs, ParsonsShift.disjoin_shift] using (ih e he hh).some
  have hu := ParsonsLogicalCases.universal A (disjoin (es.map Mark.output)) hp
  have hs : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output) ⋎ (∀⁰ A)) 🡒
      ((∀⁰ A) ⋎ disjoin (es.map Mark.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f h; simp at h ⊢; tauto)
  simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hs hu)

theorem orLeft (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q)) : Hierarchy 𝚷 2 P :=
  (Hierarchy.or_iff.mp h).1

theorem orRight (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q)) : Hierarchy 𝚷 2 Q :=
  (Hierarchy.or_iff.mp h).2

theorem andLeft (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q)) : Hierarchy 𝚷 2 P :=
  (Hierarchy.and_iff.mp h).1

theorem andRight (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q)) : Hierarchy 𝚷 2 Q :=
  (Hierarchy.and_iff.mp h).2

theorem existsInstance (A : ArithmeticSemiformula ℕ 1) (t : SyntacticTerm ℒₒᵣ)
    (h : Hierarchy 𝚷 2 (∃⁰ A)) : Hierarchy 𝚷 2 (A/[t]) :=
  Hierarchy.rew (Rew.subst ![t]) (ParsonsMarkedLogical.pi_body_of_exists A h)

/-- Principal disjunction with an arbitrary marked nonprincipal context. -/
theorem marked_or (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q))
    (es : List Mark) (d : Derivation (P :: Q :: es.map Mark.formula))
    (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Mark.side P (orLeft P Q h) :: Mark.side Q (orRight P Q h) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < d.or.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side P (orLeft P Q h) :: Mark.side Q (orRight P Q h) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side (P ⋎ Q) h :: es).map Mark.output))) := by
  have hh : d.height < d.or.height := by simp
  have hp : Proof 𝗣𝗔⁻ (P ⋎ (Q ⋎ disjoin (es.map Mark.output))) := by
    simpa [Mark.formula, Mark.output, disjoin] using (ih d hc hh).some
  simpa [Mark.output, disjoin] using Nonempty.intro (disjunction P Q _ hp)

/-- Principal conjunction with two strictly smaller marked premises. -/
theorem marked_and (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q))
    (es : List Mark) (dP : Derivation (P :: es.map Mark.formula))
    (dQ : Derivation (Q :: es.map Mark.formula))
    (hcP : Derivation.IsCutFree dP) (hcQ : Derivation.IsCutFree dQ)
    (ihP : ∀ e : Derivation ((Mark.side P (andLeft P Q h) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < (dP.and dQ).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side P (andLeft P Q h) :: es).map Mark.output))))
    (ihQ : ∀ e : Derivation ((Mark.side Q (andRight P Q h) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < (dP.and dQ).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side Q (andRight P Q h) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side (P ⋏ Q) h :: es).map Mark.output))) := by
  have hp : dP.height < (dP.and dQ).height := by simp
  have hq : dQ.height < (dP.and dQ).height := by simp
  have hP : Proof 𝗣𝗔⁻ (P ⋎ disjoin (es.map Mark.output)) := by
    simpa [Mark.formula, Mark.output, disjoin] using (ihP dP hcP hp).some
  have hQ : Proof 𝗣𝗔⁻ (Q ⋎ disjoin (es.map Mark.output)) := by
    simpa [Mark.formula, Mark.output, disjoin] using (ihQ dQ hcQ hq).some
  simpa [Mark.output, disjoin] using Nonempty.intro (conjunction P Q _ hP hQ)

/-- Principal ordinary existential, with the arbitrary marked context unchanged. -/
theorem marked_exs (A : ArithmeticSemiformula ℕ 1) (h : Hierarchy 𝚷 2 (∃⁰ A))
    (es : List Mark) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation ((A/[t]) :: es.map Mark.formula)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Mark.side (A/[t]) (existsInstance A t h) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side (A/[t]) (existsInstance A t h) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.side (∃⁰ A) h :: es).map Mark.output))) := by
  have hh : d.height < d.exs.height := by simp
  have hp : Proof 𝗣𝗔⁻ ((A/[t]) ⋎ disjoin (es.map Mark.output)) := by
    simpa [Mark.formula, Mark.output, disjoin] using (ih d hc hh).some
  have he := existential A (disjoin (es.map Mark.output)) t hp
  have hs : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output) ⋎ (∃⁰ A)) 🡒
      ((∃⁰ A) ⋎ disjoin (es.map Mark.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f h; simp at h ⊢; tauto)
  simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hs he)

/-- The actual conclusion of the LK existential rule is the marked block. -/
theorem parameter_root (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    {n : ℕ} (A : ArithmeticSemiformula ℕ (1+n)) (hs : State φ A) :
    (∃⁰ (∃⁰^[n] A)) = (Mark.block φ hφ (1+n) A hs).formula := by
  exact (ParsonsBlock.closure_outer A).symm

/-- The principal existential parameter case in the marked invariant.
The conclusion and premise retain identical side projections. -/
theorem parameter_case (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    {n : ℕ} (A : ArithmeticSemiformula ℕ (1+n)) (hs : State φ A)
    (es : List Mark) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation (((∃⁰^[n] A)/[t]) :: es.map Mark.formula))
    (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Mark.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Mark.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ (1+n) A hs :: es).map Mark.output))) := by
  have heq : ((∃⁰^[n] A)/[t]) :: es.map Mark.formula =
      (Mark.block φ hφ (0+n) (advance A t) (step φ A t hs) :: es).map Mark.formula := by
    simp only [List.map_cons, Mark.formula]
    rw [ParsonsBlock.opening]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.exs.height := by simp [e]
  simpa [Mark.output] using ih e he hh

def baseMark (ψ : ArithmeticSemiformula ℕ 1) (hψ : Hierarchy 𝚺 1 ψ) : Mark :=
  .side (base ψ) ((ParsonsSide.base_sigma ψ hψ).strict_mono _ (by decide))

def stepMark (ψ : ArithmeticSemiformula ℕ 1) (hψ : Hierarchy 𝚺 1 ψ) : Mark :=
  .side (step ψ) (ParsonsSide.step_pi_two ψ hψ)

def negativeMark (ψ : ArithmeticSemiformula ℕ 1) (t : SyntacticTerm ℒₒᵣ)
    (hψ : Hierarchy 𝚺 1 ψ) : Mark :=
  .side (∼(ψ/[t])) ((Hierarchy.neg (Hierarchy.rew (Rew.subst ![t]) hψ)).mono (by decide))

/-- The principal counter-witness case in a marked context, provided that the
remaining projected side disjunction is already Σ₁. -/
theorem counter_case (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (A : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ A))
    (es : List Mark) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation ((A/[t]) :: es.map Mark.formula)) (hc : Derivation.IsCutFree d)
    (hE : Hierarchy 𝚺 1 (disjoin (es.map Mark.output)))
    (ihBase : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((baseMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((baseMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Mark.output))))
    (ihStep : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((stepMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((stepMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) :: es).map Mark.output))))
    (ihNeg : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ) (_heq : A = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((negativeMark ((Rew.rewrite f).q ▹ φ) t (Hierarchy.rew _ hφ) :: es).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((negativeMark ((Rew.rewrite f).q ▹ φ) t (Hierarchy.rew _ hφ) :: es).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ A) hs :: es).map Mark.output))) := by
  obtain ⟨f, hf⟩ := ParsonsBlock.finish φ (∃⁰ A) hs
  have hA : A = matrix ((Rew.rewrite f).q ▹ φ) := by simpa using hf
  let ψ : ArithmeticSemiformula ℕ 1 := (Rew.rewrite f).q ▹ φ
  have hψ : Hierarchy 𝚺 1 ψ := Hierarchy.rew _ hφ
  have deq : (A/[t]) :: es.map Mark.formula = (matrix ψ)/[t] :: es.map Mark.formula := by
    rw [hA]
  let d' := d.cast deq
  have hc' : Derivation.IsCutFree d' := by simpa [d'] using hc
  have hheight : d'.exs.height = d.exs.height := by simp [d']
  have hresult : Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output))) :=
    one_case ψ (disjoin (es.map Mark.output)) t (es.map Mark.formula) d' hc' hψ hE
      (by
        intro e he hh
        have hr := ihBase f hA e he (by rw [← hheight]; exact hh)
        simpa [baseMark, Mark.output, disjoin] using hr)
      (by
        intro e he hh
        have hr := ihStep f hA e he (by rw [← hheight]; exact hh)
        simpa [stepMark, Mark.output, disjoin] using hr)
      (by
        intro e he hh
        have hr := ihNeg f hA e he (by rw [← hheight]; exact hh)
        simpa [negativeMark, Mark.output, disjoin] using hr)
  have hw : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output)) 🡒 (⊥ ⋎ disjoin (es.map Mark.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simp [hf])
  simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hw hresult.some)

end DiophantineConsistency.ParsonsUnified
