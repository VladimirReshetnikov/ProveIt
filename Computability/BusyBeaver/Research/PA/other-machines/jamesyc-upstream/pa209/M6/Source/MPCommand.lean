module
public import M6.Source.MPPrelude
public import M6.Source.MPSuccessPush
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Source.MP

private theorem return_row : resolveAt exactSites 3910 = some (.jump (some 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl

theorem return_to_root (t w d h l : Nat) (f : Registers) :
    Steps exactSites 1 (config 3910 t w d h l f) (config 0 t w d h l f) := by
  apply Steps.cons
  change Steps exactSites 0 (step exactSites ⟨.at 3910,registers t w d h l f⟩) _
  rw [step_of_resolved return_row]
  exact Steps.refl _

theorem success (w d l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (config 3884 0 w d 0 l f)
      (config 0 d (Cantor.pair 0 w) d 0 l f) := by
  obtain ⟨np,hp,sp⟩ := MPSuccessPush.push 0 w (registers 0 0 d 0 l f)
  have a : Steps exactSites np (config 3884 0 w d 0 l f)
      (config 3903 0 (Cantor.pair 0 w) d 0 l f) := by
    simpa only [push_registers,config] using sp
  have b : Steps exactSites (7*d+2) (config 3903 0 (Cantor.pair 0 w) d 0 l f)
      (config 3910 d (Cantor.pair 0 w) d 0 l f) := by
    simpa only [CopyToT.config,copy_registers,Nat.zero_add,config]
      using MPCopy.last_copy d 0 (registers 0 (Cantor.pair 0 w) 0 0 l f)
  exact ⟨np+(7*d+2)+1,by omega,(a.append b).append (return_to_root _ _ _ _ _ _)⟩

/-- COMPLETE actual MP macro3804–3910. It consumes the offset field, tests
I(T,D+offset)=H, and implements both success and failure stack effects. All
unrelated registers are preserved, X=Y=H=0 at return to actual source ordinal0.
No macro-correctness or arithmetic interpreter assumption is used. -/
theorem command (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (config 3804 t w d h l f)
      (config 0
        (if AXCode.wim t (d+(Cantor.decode l).1) = h then d+(Cantor.decode l).1 else 0)
        (if AXCode.wim t (d+(Cantor.decode l).1) = h then Cantor.pair 0 w else w)
        (d+(Cantor.decode l).1) 0 (Cantor.decode l).2 f) := by
  obtain ⟨np,hp,sp⟩ := to_guard_result t w d h l f
  by_cases hc : AXCode.wim t (d+(Cantor.decode l).1) = h
  · simp only [hc,↓reduceIte] at sp ⊢
    obtain ⟨ns,hs,ss⟩ := success w (d+(Cantor.decode l).1) (Cantor.decode l).2 f
    exact ⟨np+ns,by omega,sp.append ss⟩
  · simp only [hc,↓reduceIte] at sp ⊢
    exact ⟨np+1,by omega,sp.append (return_to_root _ _ _ _ _ _)⟩

/-- The command interface with an explicitly encoded next operand field. -/
theorem command_field (t w d h x tail : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      (config 3804 t w d h (Cantor.pair x tail) f)
      (config 0 (if AXCode.wim t (d+x) = h then d+x else 0)
        (if AXCode.wim t (d+x) = h then Cantor.pair 0 w else w)
        (d+x) 0 tail f) := by
  simpa only [Cantor.decode_pair] using command t w d h (Cantor.pair x tail) f

#print axioms command
#print axioms command_field
end M6.Source.MP

