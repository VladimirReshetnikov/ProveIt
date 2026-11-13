module
public import M6.Source.MPStore
@[expose] public section
namespace M6.Source.MP

/-- Actual MP push/copy/constructor prefix, keeping the decoded offset D.
The stack is restored after extracting the just-pushed antecedent. -/
theorem pre_guard (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (config 3818 t w d h l f)
      (config 3871 (AXCode.wim t d) w d h l f) := by
  obtain ⟨np,hp,sp⟩ := MPPush.push t w (registers 0 0 d h l f)
  have a : Steps exactSites np (config 3818 t w d h l f)
      (config 3837 0 (Cantor.pair t w) d h l f) := by
    simpa only [push_registers,config] using sp
  have b : Steps exactSites (7*d+2) (config 3837 0 (Cantor.pair t w) d h l f)
      (config 3844 d (Cantor.pair t w) d h l f) := by
    simpa only [CopyToT.config,copy_registers,Nat.zero_add,config]
      using MPCopy.first_copy d 0 (registers 0 (Cantor.pair t w) 0 h l f)
  obtain ⟨nc,hc,sc⟩ := MPCons.cons d (Cantor.pair t w) (registers 0 0 d h l f)
  have c : Steps exactSites nc (config 3844 d (Cantor.pair t w) d h l f)
      (config 3871 (AXCode.wim t d) w d h l f) := by
    simpa only [push_registers,Cantor.decode_pair,config] using sc
  exact ⟨np+(7*d+2)+nc,by omega,(a.append b).append c⟩

/-- Field decode through the actual equality decision. The only remaining
successful branch is the zero-push and D restoration after ordinal3884. -/
theorem to_guard_result (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (config 3804 t w d h l f)
      (config (if AXCode.wim t (d+(Cantor.decode l).1) = h then 3884 else 3910)
        0 w (d+(Cantor.decode l).1) 0 (Cantor.decode l).2 f) := by
  obtain ⟨nf,hf,hfu,sf⟩ := MPField.read l d (registers t w 0 h 0 f)
  have a : Steps exactSites nf (config 3804 t w d h l f)
      (config 3818 t w (d+(Cantor.decode l).1) h (Cantor.decode l).2 f) := by
    simpa only [field_registers,config] using sf
  obtain ⟨np,hp,sp⟩ := pre_guard t w (d+(Cantor.decode l).1) h (Cantor.decode l).2 f
  obtain ⟨ng,hg,sg⟩ := MPGuard.guard (AXCode.wim t (d+(Cantor.decode l).1)) h
    (registers 0 w (d+(Cantor.decode l).1) 0 (Cantor.decode l).2 f)
  have c : Steps exactSites ng
      (config 3871 (AXCode.wim t (d+(Cantor.decode l).1)) w
        (d+(Cantor.decode l).1) h (Cantor.decode l).2 f)
      (config (if AXCode.wim t (d+(Cantor.decode l).1) = h then 3884 else 3910)
        0 w (d+(Cantor.decode l).1) 0 (Cantor.decode l).2 f) := by
    simpa only [MPGuard.config,guard_registers,config] using sg
  exact ⟨nf+np+ng,by omega,(a.append sp).append c⟩
#print axioms to_guard_result
end M6.Source.MP

