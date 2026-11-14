import PA194EncodedWord
import M6.Source.Enumeration
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Fairness
open M6.Source.Cantor PA194CommandRun PA194CommandEquiv PA194FetchCommand PA194FetchSource

theorem parse_next_le (n : Nat) : (parse n).next ≤ n := by
  have h1 := (M6.Source.Enumeration.decode_bounds n).2
  have h2 := (M6.Source.Enumeration.decode_bounds (decode n).2).2
  have h3 := (M6.Source.Enumeration.decode_bounds (decode (decode n).2).2).2
  simp only [parse]
  split <;> simp_all <;> omega

theorem next_fields {s s' : State} (h : PA194CommandRun.advance s = some s') :
    s'.n = FetchDispatch.nextN s.n s.l ∧ s'.l = (parse (FetchDispatch.seed s.n s.l)).next := by
  cases hs : PA194CommandTransfer.step (parse (FetchDispatch.seed s.n s.l)).command s.store with
  | none => simp [PA194CommandRun.advance,hs] at h
  | some out =>
    simp only [PA194CommandRun.advance,hs,Option.some.injEq] at h
    subst s'
    exact ⟨rfl,rfl⟩

theorem nohalt_next {s s' : State} (h : ¬ Halts s) (ha : PA194CommandRun.advance s = some s') :
    ¬ Halts s' := by
  rintro ⟨k,final,hk,hfinal⟩
  apply h
  refine ⟨k+1,final,?_,hfinal⟩
  simpa only [PA194CommandRun.run,ha,Option.bind_some] using hk

theorem run_add (k m : Nat) (s : State) :
    PA194CommandRun.run (k+m) s = (PA194CommandRun.run k s).bind (PA194CommandRun.run m) := by
  induction k generalizing s with
  | zero => simp [PA194CommandRun.run]
  | succ k ih =>
    simp only [Nat.succ_add,PA194CommandRun.run]
    cases h : PA194CommandRun.advance s <;> simp [h,ih]

theorem nohalt_run {s s' : State} (k : Nat) (h : ¬ Halts s)
    (hr : PA194CommandRun.run k s = some s') : ¬ Halts s' := by
  intro hh
  obtain ⟨m,final,hm,hfinal⟩ := hh
  apply h
  refine ⟨k+m,final,?_,hfinal⟩
  simpa only [run_add,hr,Option.bind_some] using hm

theorem drain (s : State) (h : ¬ Halts s) :
    ∃ k s', PA194CommandRun.run k s = some s' ∧ s'.n = s.n ∧ s'.l = 0 := by
  have aux : ∀ l : Nat, ∀ s : State, s.l = l → ¬ Halts s →
      ∃ k s', PA194CommandRun.run k s = some s' ∧ s'.n = s.n ∧ s'.l = 0 := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro s hsl hnot
      by_cases hz : s.l = 0
      · exact ⟨0,s,rfl,rfl,hz⟩
      · cases ha : PA194CommandRun.advance s with
        | none => exact False.elim (hnot ⟨0,s,rfl,ha⟩)
        | some next =>
          have hf := next_fields ha
          have hn : next.n = s.n := by simpa [FetchDispatch.nextN,hz] using hf.1
          have hl : next.l < l := by
            have hb := parse_next_le (s.l-1)
            have he : next.l = (parse (s.l-1)).next := by simpa [FetchDispatch.seed,hz] using hf.2
            omega
          obtain ⟨k,last,hk,hnlast,hllast⟩ := ih next.l hl next rfl (nohalt_next hnot ha)
          refine ⟨k+1,last,?_,?_,hllast⟩
          · simpa only [PA194CommandRun.run,ha,Option.bind_some] using hk
          · exact hnlast.trans hn
  exact aux s.l s rfl h

theorem reach_fresh (distance : Nat) (s : State) (h : ¬ Halts s) :
    ∃ k last, PA194CommandRun.run k s = some last ∧ last.n = s.n+distance ∧ last.l = 0 := by
  induction distance generalizing s with
  | zero =>
    obtain ⟨k,last,hk,hn,hl⟩ := drain s h
    exact ⟨k,last,hk,by simpa using hn,hl⟩
  | succ distance ih =>
    obtain ⟨k,empty,hk,hn,hl⟩ := drain s h
    have he : ¬ Halts empty := nohalt_run k h hk
    cases ha : PA194CommandRun.advance empty with
    | none => exact False.elim (he ⟨0,empty,rfl,ha⟩)
    | some next =>
      have hf := next_fields ha
      have hnext : next.n = s.n+1 := by simpa [FetchDispatch.nextN,hl,hn] using hf.1
      obtain ⟨m,last,hm,hnlast,hllast⟩ := ih next (nohalt_next he ha)
      have hprefix : PA194CommandRun.run (k+1) s = some next := by
        rw [run_add]
        simp only [hk,Option.bind_some]
        simp [PA194CommandRun.run,ha]
      refine ⟨(k+1)+m,last,?_,?_,hllast⟩
      · simpa only [run_add,hprefix,Option.bind_some] using hm
      · omega

theorem encodeCommand_tail_le (c : PA196.Commands.Command) (tail : Nat) :
    tail ≤ PA194EncodedWord.encodeCommand c tail := by
  cases c with
  | shift => exact (M6.Source.Enumeration.pair_bounds 0 tail).2
  | mp x =>
    have h1 := (M6.Source.Enumeration.pair_bounds x tail).2
    have h2 := (M6.Source.Enumeration.pair_bounds 1 (pair x tail)).2
    simpa [PA194EncodedWord.encodeCommand] using Nat.le_trans h1 h2
  | ax c x y =>
    have h1 := (M6.Source.Enumeration.pair_bounds x tail).2
    have h2 := (M6.Source.Enumeration.pair_bounds y (pair x tail)).2
    have h3 := (M6.Source.Enumeration.pair_bounds (c+2) (pair y (pair x tail))).2
    simpa [PA194EncodedWord.encodeCommand] using Nat.le_trans (Nat.le_trans h1 h2) h3

theorem encodeWord_tail_le (cs : List PA196.Commands.Command) (tail : Nat) :
    tail ≤ PA194EncodedWord.encodeWord cs tail := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    have h := encodeCommand_tail_le c (PA194EncodedWord.encodeWord cs tail)
    simp only [PA194EncodedWord.encodeWord]
    omega

theorem fresh_same_advance (n : Nat) (s : PA196.Commands.Store) :
    PA194CommandRun.advance ⟨n,0,s⟩ = PA194CommandRun.advance ⟨n+1,n+1,s⟩ := by
  simp [PA194CommandRun.advance,FetchDispatch.seed,FetchDispatch.nextN]

theorem same_advance_halts {s s' : State}
    (he : PA194CommandRun.advance s = PA194CommandRun.advance s') (h : Halts s') : Halts s := by
  obtain ⟨k,last,hk,hlast⟩ := h
  cases k with
  | zero =>
    simp only [PA194CommandRun.run,Option.some.injEq] at hk
    subst last
    refine ⟨0,s,rfl,?_⟩
    exact he.trans hlast
  | succ k =>
    refine ⟨k+1,last,?_,hlast⟩
    simpa only [PA194CommandRun.run,he] using hk

theorem derivation_halts_initial (p : PA194DerivationCompiler.Derivation 1) :
    Halts ⟨2,0,⟨0,0,0,0⟩⟩ := by
  by_cases h : Halts ⟨2,0,⟨0,0,0,0⟩⟩
  · exact h
  · let word := PA194DerivationCompiler.haltWord p
    let code := PA194EncodedWord.encodeWord word 3
    let candidate := code-1
    have hcode : 3 ≤ code := encodeWord_tail_le word 3
    have hnonempty : word ≠ [] := by simp [word,PA194DerivationCompiler.haltWord]
    have hpositive : 0 < code := by omega
    have hcandidate : 2 ≤ candidate := by dsimp [candidate]; omega
    obtain ⟨k,st,hk,hn,hl⟩ := reach_fresh (candidate-2) ⟨2,0,⟨0,0,0,0⟩⟩ h
    have hn' : st.n = candidate := by simp only at hn; omega
    have hpointer := PA194EncodedWord.derivation_halts_scheduler p 3 (candidate+1) st.store
    have hcode' : code = candidate+1 := by dsimp [candidate]; omega
    have hpointer' : Halts ⟨candidate+1,candidate+1,st.store⟩ := by
      simpa only [word,←hcode',code] using hpointer
    have hfresh : Halts ⟨candidate,0,st.store⟩ :=
      same_advance_halts (fresh_same_advance candidate st.store) hpointer'
    have heq : st = ⟨candidate,0,st.store⟩ := by
      cases st with
      | mk n l store => simp_all
    exact False.elim ((nohalt_run k h hk) (heq ▸ hfresh))

#print axioms derivation_halts_initial
#print axioms reach_fresh
#print axioms parse_next_le
#print axioms drain
end PA194Fairness
