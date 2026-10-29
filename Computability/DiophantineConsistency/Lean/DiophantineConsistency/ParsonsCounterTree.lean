import DiophantineConsistency.ParsonsGuardTree
import DiophantineConsistency.ParsonsOrInvert
import DiophantineConsistency.ParsonsAndContext
import DiophantineConsistency.ParsonsBooleanOutput
import DiophantineConsistency.ParsonsFreshContext
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCounterTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsBlock ParsonsStructure ParsonsRule ParsonsInductionCase
open ParsonsGuardPrefix ParsonsGuardTree

private noncomputable def drop_bottom (E : Proposition ℒₒᵣ) (h : Proof 𝗣𝗔⁻ (⊥ ⋎ E)) : Proof 𝗣𝗔⁻ E :=
  Proof.mp (ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa using hf)) h

private noncomputable def add_bottom (E : Proposition ℒₒᵣ) (h : Proof 𝗣𝗔⁻ E) : Proof 𝗣𝗔⁻ (⊥ ⋎ E) :=
  Proof.mp (ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa using hf)) h

/-- Counterexample case with any finite list of positive Boolean guarded sides.
`Below H` is the explicit strong derivation hypothesis, not a theorem here. -/
theorem counter_tree (n : ℕ) :
    ∀ (es : List Mark), nodeCost es < n → Good es →
    ∀ (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
      (B : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ B))
      (t : SyntacticTerm ℒₒᵣ) (d : Derivation (B/[t] :: es.map Mark.formula)),
      Derivation.IsCutFree d → ∀ H : ℕ, d.exs.height ≤ H → Below H →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ B) hs :: es).map Mark.output))) := by
  induction n with
  | zero => intro es hn; omega
  | succ n ih =>
      intro es hn hgood φ hφ B hs t d hc H hd hbelow
      cases choose es hgood with
      | sigma hE =>
        apply counter_case φ hφ B hs es t d hc hE
        · intro f eq e he ht; exact hbelow _ e he (lt_of_lt_of_le ht hd)
        · intro f eq e he ht; exact hbelow _ e he (lt_of_lt_of_le ht hd)
        · intro f eq e he ht; exact hbelow _ e he (lt_of_lt_of_le ht hd)
      | all left right A hA ha heq =>
        subst es
        let es' := left.map Mark.shift ++ Mark.side A.free ha.pi :: right.map Mark.shift
        have hL : Good left := by
          intro e he; exact hgood e (by simp [he])
        have hR : Good right := by
          intro e he; exact hgood e (by simp [he])
        have hgood' : Good es' := by
          intro e he
          simp only [es', List.mem_append, List.mem_cons] at he
          rcases he with h | rfl | h
          · exact shift_good left hL e h
          · exact ha
          · exact shift_good right hR e h
        have hcost : nodeCost es' < n := by
          have hcst := nodes_all left right A hA ha
          dsimp [es']
          omega
        have deq : B/[t] :: (left ++ Mark.side (∀⁰ A) hA :: right).map Mark.formula =
            B/[t] :: (left.map Mark.formula ++ (∀⁰ A) :: right.map Mark.formula) := by
          simp [Mark.formula]
        let d' := d.cast deq
        have hfree : Derivation.IsCutFree d' := by simpa [d'] using hc
        obtain ⟨e, he, ht⟩ := ParsonsFreshContext.fresh_open_at A B t
          (left.map Mark.formula) (right.map Mark.formula) d' hfree
        have hsub : Rewriting.shift (B/[t]) = (Rew.shift ▹ B)/[Rew.shift t] := by
          have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) = (@Rew.shift ℒₒᵣ 0) := by ext i <;> simp
          simpa [hr, ← Rew.q_rewrite] using
            (LawfulSyntacticRewriting.rewrite_subst_eq (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) t B)
        have eeq : (Rewriting.shift (B/[t]) ::
            ((left.map Mark.formula)⁺ ++ A.free :: (right.map Mark.formula)⁺)) =
            ((Rew.shift ▹ B)/[Rew.shift t]) :: es'.map Mark.formula := by
          simp only [es', List.map_append, List.map_cons, Mark.formula, shift_formulas, hsub]
        let e' := e.cast eeq
        have hf' : Derivation.IsCutFree e' := by simpa [e'] using he
        have hh : e'.exs.height ≤ H := by
          simp only [e', Derivation.height_exs, Derivation.height_cast, d'] at *
          omega
        have hS : State φ (∃⁰ (Rew.shift ▹ B)) := by
          simpa using ParsonsShift.state_shift φ (∃⁰ B) hs
        have hp := ih es' hcost hgood' φ hφ (Rew.shift ▹ B) hS (Rew.shift t) e' hf' H hh hbelow
        have hp1 : Proof 𝗣𝗔⁻ (⊥ ⋎ disjoin (es'.map Mark.output)) := by
          simpa only [List.map_cons, Mark.output, disjoin] using hp.some
        have hdrop : Proof 𝗣𝗔⁻ ((⊥ ⋎ disjoin (es'.map Mark.output)) 🡒 disjoin (es'.map Mark.output)) :=
          ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa using hf)
        have hp0 := Proof.mp hdrop hp1
        have hsubset : es'.map Mark.output ⊆ A.free :: ((left ++ right).map Mark.shift).map Mark.output := by
          intro P hP
          simp only [es', List.map_append, List.map_cons, Mark.output, List.mem_append, List.mem_cons] at hP ⊢
          tauto
        have hp2 := weakening _ _ hsubset hp0
        let E := disjoin ((left ++ right).map Mark.output)
        have hout : Proof 𝗣𝗔⁻ (A.free ⋎ Rewriting.shift E) := by
          simpa only [List.map_cons, disjoin, shift_outputs, ParsonsShift.disjoin_shift, E] using hp2
        have hu := ParsonsLogicalCases.universal A E hout
        have hin : Proof 𝗣𝗔⁻ ((E ⋎ (∀⁰ A)) 🡒 disjoin ((left ++ Mark.side (∀⁰ A) hA :: right).map Mark.output)) :=
          ParsonsGuardedCollection.of_semantics _ _ (by
            intro M _ _ f hf
            simp only [LogicalConnective.HomClass.map_or] at hf
            rw [eval_disjoin]
            rcases hf with hE | hA'
            · rw [eval_disjoin] at hE
              obtain ⟨P, hP, hval⟩ := hE
              refine ⟨P, ?_, hval⟩
              simp only [List.map_append, List.map_cons, Mark.output, List.mem_append, List.mem_cons] at hP ⊢
              tauto
            · refine ⟨∀⁰ A, ?_, hA'⟩
              simp [Mark.output])
        have hfinal : Proof 𝗣𝗔⁻ (disjoin ((left ++ Mark.side (∀⁰ A) hA :: right).map Mark.output) 🡒
            (⊥ ⋎ disjoin ((left ++ Mark.side (∀⁰ A) hA :: right).map Mark.output))) :=
          ParsonsGuardedCollection.of_semantics _ _ (by
            intro M _ _ f hf
            simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_bot]
            exact Or.inr hf)
        simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hfinal (Proof.mp hin hu))
      | or left right P Q hP hQ heq =>
        subst es
        let es' := left ++ Mark.side P hP.pi :: Mark.side Q hQ.pi :: right
        have hL : Good left := by intro e he; exact hgood e (by simp [he])
        have hR : Good right := by intro e he; exact hgood e (by simp [he])
        have hgood' : Good es' := by
          intro e he
          simp only [es', List.mem_append, List.mem_cons] at he
          rcases he with h | rfl | rfl | h
          · exact hL e h
          · exact hP
          · exact hQ
          · exact hR e h
        have hcost : nodeCost es' < n := by
          have hcst := nodes_or left right P Q hP.pi hQ.pi
          dsimp [es']
          omega
        have deq : B/[t] :: (left ++ Mark.side (P ⋎ Q) (Hierarchy.or hP.pi hQ.pi) :: right).map Mark.formula =
            B/[t] :: (left.map Mark.formula ++ (P ⋎ Q) :: right.map Mark.formula) := by simp [Mark.formula]
        let d' := d.cast deq
        have hfree : Derivation.IsCutFree d' := by simpa [d'] using hc
        obtain ⟨e, he, ht⟩ := ParsonsOrInvert.invert_below_exs P Q B t
          (left.map Mark.formula) (right.map Mark.formula) d' hfree
        have eeq : (B/[t] :: (left.map Mark.formula ++ P :: Q :: right.map Mark.formula)) =
            B/[t] :: es'.map Mark.formula := by simp [es', Mark.formula]
        let e' := e.cast eeq
        have hf' : Derivation.IsCutFree e' := by simpa [e'] using he
        have hh : e'.exs.height ≤ H := by
          simp only [e', Derivation.height_exs, Derivation.height_cast, d'] at *
          omega
        have hp := ih es' hcost hgood' φ hφ B hs t e' hf' H hh hbelow
        have hp' : Proof 𝗣𝗔⁻ (disjoin (left.map Mark.output ++ P :: Q :: right.map Mark.output)) := by
          have raw : Proof 𝗣𝗔⁻ (⊥ ⋎ disjoin (es'.map Mark.output)) := by
            simpa only [List.map_cons, Mark.output, disjoin] using hp.some
          simpa [es', Mark.output] using drop_bottom _ raw
        have hmerged := ParsonsBooleanOutput.collapse_or (left.map Mark.output) (right.map Mark.output) P Q hp'
        simpa [Mark.output, disjoin] using Nonempty.intro (add_bottom _ hmerged)
      | and left right P Q hP hQ heq =>
        subst es
        have hL : Good left := by intro e he; exact hgood e (by simp [he])
        have hR : Good right := by intro e he; exact hgood e (by simp [he])
        have branch (C : Proposition ℒₒᵣ) (hC : Tree C) (hwhich : C = P ∨ C = Q) :
            Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ B) hs ::
              (left ++ Mark.side C hC.pi :: right)).map Mark.output))) := by
          let es' := left ++ Mark.side C hC.pi :: right
          have hgood' : Good es' := by
            intro e he
            simp only [es', List.mem_append, List.mem_cons] at he
            rcases he with h | rfl | h
            · exact hL e h
            · exact hC
            · exact hR e h
          have hcost : nodeCost es' < n := by
            rcases hwhich with h | h
            · subst C
              have hcst := (nodes_and left right P Q hP.pi hQ.pi).1
              dsimp [es']
              omega
            · subst C
              have hcst := (nodes_and left right P Q hP.pi hQ.pi).2
              dsimp [es']
              omega
          have deq : B/[t] :: (left ++ Mark.side (P ⋏ Q) (Hierarchy.and hP.pi hQ.pi) :: right).map Mark.formula =
              B/[t] :: (left.map Mark.formula ++ (P ⋏ Q) :: right.map Mark.formula) := by simp [Mark.formula]
          let d' := d.cast deq
          have hfree : Derivation.IsCutFree d' := by simpa [d'] using hc
          obtain ⟨e, he, ht⟩ := ParsonsAndContext.invert_below_exs P Q C hwhich B t
            (left.map Mark.formula) (right.map Mark.formula) d' hfree
          have eeq : (B/[t] :: (left.map Mark.formula ++ C :: right.map Mark.formula)) =
              B/[t] :: es'.map Mark.formula := by simp [es', Mark.formula]
          let e' := e.cast eeq
          have hf' : Derivation.IsCutFree e' := by simpa [e'] using he
          have hh : e'.exs.height ≤ H := by
            simp only [e', Derivation.height_exs, Derivation.height_cast, d'] at *
            omega
          exact ih es' hcost hgood' φ hφ B hs t e' hf' H hh hbelow
        have hp := branch P hP (Or.inl rfl)
        have hq := branch Q hQ (Or.inr rfl)
        have hp' : Proof 𝗣𝗔⁻ (disjoin (left.map Mark.output ++ P :: right.map Mark.output)) := by
          have raw : Proof 𝗣𝗔⁻ (⊥ ⋎ disjoin ((left ++ Mark.side P hP.pi :: right).map Mark.output)) := by
            simpa only [List.map_cons, Mark.output, disjoin] using hp.some
          simpa [Mark.output] using drop_bottom _ raw
        have hq' : Proof 𝗣𝗔⁻ (disjoin (left.map Mark.output ++ Q :: right.map Mark.output)) := by
          have raw : Proof 𝗣𝗔⁻ (⊥ ⋎ disjoin ((left ++ Mark.side Q hQ.pi :: right).map Mark.output)) := by
            simpa only [List.map_cons, Mark.output, disjoin] using hq.some
          simpa [Mark.output] using drop_bottom _ raw
        have hmerged := ParsonsBooleanOutput.collapse_and (left.map Mark.output) (right.map Mark.output) P Q hp' hq'
        simpa [Mark.output, disjoin] using Nonempty.intro (add_bottom _ hmerged)
/-- Fuel-free interface for the same conditional local case. -/
theorem counter_tree_unbounded (es : List Mark) (hgood : Good es)
    (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (B : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ B))
    (t : SyntacticTerm ℒₒᵣ) (d : Derivation (B/[t] :: es.map Mark.formula))
    (hc : Derivation.IsCutFree d) (H : ℕ) (hd : d.exs.height ≤ H) (hbelow : Below H) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ B) hs :: es).map Mark.output))) :=
  counter_tree (nodeCost es + 1) es (by omega) hgood φ hφ B hs t d hc H hd hbelow
end DiophantineConsistency.ParsonsCounterTree
