import DiophantineConsistency.ParsonsCounterStable
import DiophantineConsistency.ParsonsTreeLogical
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGlobalStrict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsRule ParsonsStructure ParsonsBlock
open ParsonsGuardTree ParsonsStrictInvariant ParsonsBaseInvariant ParsonsCounterStable

def Stable (es : List Mark) : Prop := Good es ∧ StrictBlocks es ∧ BaseGood es

theorem stable_shift (es : List Mark) (h : Stable es) : Stable (es.map Mark.shift) :=
  ⟨ParsonsGuardTree.shift_good es h.1, shift_blocks es h.2.1, ParsonsBaseInvariant.shift_good es h.2.2⟩

theorem stable_select (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) (h : Stable es) : Stable (selectEntries Δ es hsub) :=
  ⟨ParsonsTreeLogical.good_select Δ es hsub h.1, select_blocks Δ es hsub h.2.1,
    ParsonsBaseInvariant.select_good Δ es hsub h.2.2⟩

theorem stable_tail (e : Mark) (es : List Mark) (h : Stable (e :: es)) : Stable es := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha
  · exact h.1 a (by simp [ha])
  · exact h.2.1 a (by simp [ha])
  · exact h.2.2 a (by simp [ha])

theorem stable_side (P : Proposition ℒₒᵣ) (hp : Hierarchy 𝚷 2 P) (hP : Tree P)
    (es : List Mark) (h : Stable es) : Stable (Mark.side P hp :: es) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha <;> simp only [List.mem_cons] at ha
  · rcases ha with rfl | ha
    · exact hP
    · exact h.1 a ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.2.1 a ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.2.2 a ha

theorem stable_base (s : ParsonsBaseShape.ShapedBase) (hp : ParsonsBasePositive.Prefix s.state.positive)
    (es : List Mark) (h : Stable es) : Stable (Mark.base s :: es) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha <;> simp only [List.mem_cons] at ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.1 a ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.2.1 a ha
  · rcases ha with rfl | ha
    · exact hp
    · exact h.2.2 a ha

theorem stable_block (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (n : ℕ) (A : ArithmeticSemiformula ℕ n) (hA : State φ A) (hstrict : Strict φ)
    (es : List Mark) (h : Stable es) : Stable (Mark.block φ hφ n A hA :: es) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha <;> simp only [List.mem_cons] at ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.1 a ha
  · rcases ha with rfl | ha
    · exact hstrict
    · exact h.2.1 a ha
  · rcases ha with rfl | ha
    · trivial
    · exact h.2.2 a ha

theorem state_cast {n m : ℕ} (e : n = m) (φ : ArithmeticSemiformula ℕ 1)
    (A : ArithmeticSemiformula ℕ n) (h : State φ A) :
    State φ (cast (congrArg (ArithmeticSemiformula ℕ) e) A) := by
  cases e
  exact h

theorem exs_closure_cast {n m : ℕ} (e : n = m) (A : ArithmeticSemiformula ℕ n) :
    (∃⁰* cast (congrArg (ArithmeticSemiformula ℕ) e) A) = ∃⁰* A := by
  cases e
  rfl

/-- Height is the primary recursion measure, with marked base count secondary
for same-height terminal reclassification. -/
theorem translate_aux (H : ℕ) :
    ∀ K : ℕ, ∀ (es : List Mark) (d : Derivation (es.map Mark.formula)),
      Stable es → Derivation.IsCutFree d → d.height < H → baseCount es < K →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output))) := by
  induction H with
  | zero => intro K es d hs hc hh; omega
  | succ H ih =>
      intro K
      induction K with
      | zero => intro es d hs hc hh hk; omega
      | succ K ihK =>
        intro es d hs hc hh hk
        have lower : BelowStable H := by
          intro es' hgood hblocks hbases e he heh
          exact ih (baseCount es' + 1) es' e ⟨hgood,hblocks,hbases⟩ he heh (by omega)
        cases es with
        | nil =>
            exact ⟨base_branch [] (by simp) d⟩
        | cons e es =>
            cases e with
            | side P hp =>
                generalize hΓ : (Mark.side P hp :: es).map Mark.formula = Γ at d hc
                cases hc with
                | identity r v => exact ⟨ParsonsLeaves.identity_leaf r v _ hΓ⟩
                | verum => exact ⟨ParsonsLeaves.verum_leaf _ hΓ⟩
                | @or φ ψ Γ d hc =>
                    simp only [List.map_cons, Mark.formula, List.cons.injEq] at hΓ
                    obtain ⟨hP,hTail⟩ := hΓ
                    subst P
                    subst Γ
                    have htree : Tree (φ ⋎ ψ) := hs.1 (Mark.side (φ ⋎ ψ) hp) (by simp)
                    obtain ⟨htφ,htψ⟩ := ParsonsTreeLogical.or_parts φ ψ htree
                    have hst := stable_tail _ es hs
                    have hnew := stable_side φ (orLeft φ ψ hp) htφ _
                      (stable_side ψ (orRight φ ψ hp) htψ es hst)
                    apply marked_or φ ψ hp es d hc
                    intro e he hlt
                    exact lower _ hnew.1 hnew.2.1 hnew.2.2 e he (lt_of_lt_of_le hlt (by omega))
                | @and φ Γ ψ dφ dψ hc1 hc2 =>
                    simp only [List.map_cons, Mark.formula, List.cons.injEq] at hΓ
                    obtain ⟨hP,hTail⟩ := hΓ
                    subst P
                    subst Γ
                    have htree : Tree (φ ⋏ ψ) := hs.1 (Mark.side (φ ⋏ ψ) hp) (by simp)
                    obtain ⟨htφ,htψ⟩ := ParsonsTreeLogical.and_parts φ ψ htree
                    have hst := stable_tail _ es hs
                    have hnewφ := stable_side φ (andLeft φ ψ hp) htφ es hst
                    have hnewψ := stable_side ψ (andRight φ ψ hp) htψ es hst
                    apply marked_and φ ψ hp es dφ dψ hc1 hc2
                    · intro e he hlt
                      exact lower _ hnewφ.1 hnewφ.2.1 hnewφ.2.2 e he (lt_of_lt_of_le hlt (by omega))
                    · intro e he hlt
                      exact lower _ hnewψ.1 hnewψ.2.1 hnewψ.2.2 e he (lt_of_lt_of_le hlt (by omega))
                | @all A Γ d hc =>
                    simp only [List.map_cons, Mark.formula, List.cons.injEq] at hΓ
                    obtain ⟨hP,hTail⟩ := hΓ
                    subst P
                    subst Γ
                    have htree : Tree (∀⁰ A) := hs.1 (Mark.side (∀⁰ A) hp) (by simp)
                    have hst := stable_shift es (stable_tail _ es hs)
                    have hnew := stable_side A.free (opened_pi_two A hp) (ParsonsTreeLogical.all_open A htree) _ hst
                    apply marked_universal A hp es d hc
                    intro e he hlt
                    exact lower _ hnew.1 hnew.2.1 hnew.2.2 e he (lt_of_lt_of_le hlt (by omega))
                | @exs A Γ t d hc =>
                    simp only [List.map_cons, Mark.formula, List.cons.injEq] at hΓ
                    obtain ⟨hP,hTail⟩ := hΓ
                    subst P
                    subst Γ
                    have htree : Tree (∃⁰ A) := hs.1 (Mark.side (∃⁰ A) hp) (by simp)
                    have hnew := stable_side (A/[t]) (existsInstance A t hp) (ParsonsTreeLogical.exists_instance A t htree) es (stable_tail _ es hs)
                    apply marked_exs A hp es t d hc
                    intro e he hlt
                    exact lower _ hnew.1 hnew.2.1 hnew.2.2 e he (lt_of_lt_of_le hlt (by omega))
                | @contraction Δ Γ d hsub hc =>
                    rw [← hΓ] at hsub
                    apply marked_contraction Δ (Mark.side P hp :: es) hsub d hc
                    intro e he hlt
                    have hnew := stable_select Δ (Mark.side P hp :: es) hsub hs
                    have heq := selected_formulas Δ (Mark.side P hp :: es) hsub
                    let e' := e.cast heq.symm
                    have he' : Derivation.IsCutFree e' := by simpa [e'] using he
                    have hh' : e'.height < H := by
                      simp only [e', Derivation.height_cast, Derivation.height_contraction] at *
                      omega
                    exact lower _ hnew.1 hnew.2.1 hnew.2.2 e' he' hh'
            | block φ hφ n A hA =>
                have hstrict : Strict φ := hs.2.1 (Mark.block φ hφ n A hA) (by simp)
                cases n with
                | zero =>
                    obtain ⟨f,hf⟩ := ParsonsBlock.finish φ A hA
                    subst A
                    generalize hΓ : (Mark.block φ hφ 0 (∃⁰ ParsonsInductionCase.matrix ((Rew.rewrite f).q ▹ φ)) hA :: es).map Mark.formula = Γ at d hc
                    cases hc with
                    | identity r v => exact ⟨ParsonsLeaves.identity_leaf r v _ hΓ⟩
                    | verum => exact ⟨ParsonsLeaves.verum_leaf _ hΓ⟩
                    | or hc => simp [Mark.formula] at hΓ
                    | and hc1 hc2 => simp [Mark.formula] at hΓ
                    | all hc => simp [Mark.formula] at hΓ
                    | @exs B Γ t d hc =>
                        simp only [List.map_cons, Mark.formula, exsClosure_zero, List.cons.injEq,
                          Semiformula.exs_inj] at hΓ
                        obtain ⟨hB,hTail⟩ := hΓ
                        subst B
                        subst Γ
                        have hst := stable_tail _ es hs
                        exact counter_stable_unbounded es hst.1 hst.2.1 hst.2.2 φ hφ hstrict _ hA t d hc H (by omega) lower
                    | @contraction Δ Γ d hsub hc =>
                        rw [← hΓ] at hsub
                        apply marked_contraction Δ _ hsub d hc
                        intro e he hlt
                        have hnew := stable_select Δ _ hsub hs
                        have heq := selected_formulas Δ _ hsub
                        let e' := e.cast heq.symm
                        have he' : Derivation.IsCutFree e' := by simpa [e'] using he
                        have hh' : e'.height < H := by
                          simp only [e', Derivation.height_cast, Derivation.height_contraction] at *
                          omega
                        exact lower _ hnew.1 hnew.2.1 hnew.2.2 e' he' hh'
                | succ n =>
                    let eq : n+1 = 1+n := Nat.add_comm n 1
                    let A' : ArithmeticSemiformula ℕ (1+n) := cast (congrArg (ArithmeticSemiformula ℕ) eq) A
                    have hA' : State φ A' := state_cast eq φ A hA
                    have hclos : (∃⁰* A') = ∃⁰* A := exs_closure_cast eq A
                    have heq : (Mark.block φ hφ (n+1) A hA :: es).map Mark.formula =
                        (Mark.block φ hφ (1+n) A' hA' :: es).map Mark.formula := by
                      simp only [List.map_cons, Mark.formula, hclos]
                    let d' := d.cast heq
                    have hc' : Derivation.IsCutFree d' := by simpa [d'] using hc
                    have hh' : d'.height < H+1 := by simpa [d'] using hh
                    have hst := stable_tail _ es hs
                    have hs' := stable_block φ hφ (1+n) A' hA' hstrict es hst
                    have hr : ∀ (D : Derivation ((Mark.block φ hφ (1+n) A' hA' :: es).map Mark.formula)),
                        Derivation.IsCutFree D → D.height < H+1 →
                        Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ (1+n) A' hA' :: es).map Mark.output))) := by
                      intro D hD hDh
                      generalize hΓ : (Mark.block φ hφ (1+n) A' hA' :: es).map Mark.formula = Γ at D hD
                      cases hD with
                      | identity r v => exact ⟨ParsonsLeaves.identity_leaf r v _ hΓ⟩
                      | verum => exact ⟨ParsonsLeaves.verum_leaf _ hΓ⟩
                      | or hc => simp [Mark.formula, ParsonsBlock.closure_outer] at hΓ
                      | and hc1 hc2 => simp [Mark.formula, ParsonsBlock.closure_outer] at hΓ
                      | all hc => simp [Mark.formula, ParsonsBlock.closure_outer] at hΓ
                      | @exs B Γ t d hc =>
                          simp only [List.map_cons, Mark.formula, ParsonsBlock.closure_outer,
                            List.cons.injEq, Semiformula.exs_inj] at hΓ
                          obtain ⟨hB,hTail⟩ := hΓ
                          subst B
                          subst Γ
                          have hnew := stable_block φ hφ (0+n) (advance A' t) (ParsonsBlock.step φ A' t hA') hstrict es hst
                          apply parameter_case φ hφ A' hA' es t d hc
                          intro e he hlt
                          exact lower _ hnew.1 hnew.2.1 hnew.2.2 e he (lt_of_lt_of_le hlt (by omega))
                      | @contraction Δ Γ d hsub hc =>
                          rw [← hΓ] at hsub
                          apply marked_contraction Δ _ hsub d hc
                          intro e he hlt
                          have hnew := stable_select Δ _ hsub hs'
                          have heq := selected_formulas Δ _ hsub
                          let e' := e.cast heq.symm
                          have he' : Derivation.IsCutFree e' := by simpa [e'] using he
                          have hh' : e'.height < H := by
                            simp only [e', Derivation.height_cast, Derivation.height_contraction] at *
                            omega
                          exact lower _ hnew.1 hnew.2.1 hnew.2.2 e' he' hh'
                    simpa [Mark.output, disjoin] using hr d' hc' hh'
            | base s =>
                have hshape : ParsonsBasePositive.Prefix s.state.positive := hs.2.2 (Mark.base s) (by simp)
                generalize hpEq : s.state.positive = P at hshape
                cases hshape with
                | terminal hp =>
                    have hp' : ParsonsBasePositive.Positive s.state.positive := hpEq.symm ▸ hp
                    let hsig := ParsonsBasePositive.sigma hp'
                    let es' := Mark.side s.state.negative ((Hierarchy.neg hsig).strict_mono _ (by decide)) :: es
                    have hstable : Stable es' := ParsonsBaseInvariant.terminal_good s hp' es hs.1 hs.2.1 hs.2.2
                    have heq : (Mark.base s :: es).map Mark.formula = es'.map Mark.formula := by rfl
                    let d' := d.cast heq
                    have hc' : Derivation.IsCutFree d' := by simpa [d'] using hc
                    have hh' : d'.height < H+1 := by simpa [d'] using hh
                    have hk' : baseCount es' < K := by
                      have hm := terminal_measure s hsig es
                      dsimp [es'] at hm ⊢
                      omega
                    exact base_terminal s hsig es (ihK es' d' hstable hc' hh' hk')
                | @all _ A hp =>
                    generalize hΓ : (Mark.base s :: es).map Mark.formula = Γ at d hc
                    cases hc with
                    | identity r v => exact ⟨ParsonsLeaves.identity_leaf r v _ hΓ⟩
                    | verum => exact ⟨ParsonsLeaves.verum_leaf _ hΓ⟩
                    | or hc => simp [Mark.formula, ParsonsBaseState.BaseState.negative, hpEq] at hΓ
                    | and hc1 hc2 => simp [Mark.formula, ParsonsBaseState.BaseState.negative, hpEq] at hΓ
                    | all hc => simp [Mark.formula, ParsonsBaseState.BaseState.negative, hpEq] at hΓ
                    | @exs B Γ t d hc =>
                        simp only [List.map_cons, Mark.formula, ParsonsBaseState.BaseState.negative,
                          hpEq, Semiformula.neg_all, List.cons.injEq, Semiformula.exs_inj] at hΓ
                        obtain ⟨hB,hTail⟩ := hΓ
                        subst B
                        subst Γ
                        have hshape' : ParsonsBasePositive.Prefix (ParsonsBaseShape.openState s A hpEq t).state.positive :=
                          ParsonsBasePositive.open_state s (hpEq.symm ▸ ParsonsBasePositive.Prefix.all hp) A hpEq t
                        have hnew := stable_base _ hshape' es (stable_tail _ es hs)
                        apply base_open s A hpEq t es d hc
                        intro e he hlt
                        exact lower _ hnew.1 hnew.2.1 hnew.2.2 e he (lt_of_lt_of_le hlt (by omega))
                    | @contraction Δ Γ d hsub hc =>
                        rw [← hΓ] at hsub
                        apply marked_contraction Δ (Mark.base s :: es) hsub d hc
                        intro e he hlt
                        have hnew := stable_select Δ (Mark.base s :: es) hsub hs
                        have heq := selected_formulas Δ (Mark.base s :: es) hsub
                        let e' := e.cast heq.symm
                        have he' : Derivation.IsCutFree e' := by simpa [e'] using he
                        have hh' : e'.height < H := by
                          simp only [e', Derivation.height_cast, Derivation.height_contraction] at *
                          omega
                        exact lower _ hnew.1 hnew.2.1 hnew.2.2 e' he' hh' 
/-- Closed recursion for any cut-free derivation satisfying the three
explicit marked-context invariants. -/
theorem translate (es : List Mark) (d : Derivation (es.map Mark.formula))
    (hs : Stable es) (hc : Derivation.IsCutFree d) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output))) :=
  translate_aux (d.height + 1) (baseCount es + 1) es d hs hc (by omega) (by omega)
end DiophantineConsistency.ParsonsGlobalStrict

