import PA194ProgramCons

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace PA194ProgramCons
open PA194ProgramDrain
open M6.Source (Instruction)

/-- The common prefix decodes and restores the stack, then pairs its head and
    the old top. The last entry tests the multiplier's counter. -/
def prefixRows (base coefficient : Nat) : Fin 22 → Instruction := ![
  .dec 2 (some (base+8)) (some (base+1)),
  .inc 7 (some (base+2)),
  .dec 6 (some (base+4)) (some (base+3)),
  .jump (some (base+7)),
  .dec 7 (some (base+7)) (some (base+5)),
  .inc 6 (some (base+6)),
  .jump (some (base+4)),
  .jump (some base),
  .dec 7 (some (base+11)) (some (base+9)),
  .inc 2 (some (base+10)),
  .jump (some (base+8)),
  .dec 1 (some (base+15)) (some (base+12)),
  .inc 7 (some (base+13)),
  .inc 6 (some (base+14)),
  .jump (some (base+11)),
  .dec 6 (some (base+21)) (some (base+16)),
  .inc 7 (some (base+17)),
  .dec 6 (some (base+20)) (some (base+18)),
  .inc 1 (some (base+19)),
  .jump (some (base+17)),
  .jump (some (base+11)),
  .dec 7 (some (base+23+coefficient)) (some (base+22))
]

def Certified (program : Program) (base coefficient : Nat) : Prop :=
  base+22+coefficient < program.length ∧
  (∀ index : Fin 22, row program (base+index.val) = some (prefixRows base coefficient index)) ∧
  (∀ index : Fin coefficient,
    row program (base+22+index.val) = some (.inc 1 (some (base+22+index.val+1)))) ∧
  row program (base+22+coefficient) = some (.jump (some (base+21)))

private theorem incrementTrace {program : Program} (back first count : Nat)
    (hbound : first+count < program.length)
    (hinc : ∀ index : Fin count,
      row program (first+index.val) = some (.inc 1 (some (first+index.val+1))))
    (hback : row program (first+count) = some (.jump (some back))) :
    Increments program back first (List.replicate count (1 : Fin 9)) := by
  induction count generalizing first with
  | zero =>
    exact .jump first (by simpa using hbound) (by simpa using hback)
  | succ count ih =>
    apply Increments.inc first (first+1) 1 (List.replicate count 1) (by omega)
    · simpa using hinc ⟨0, by omega⟩
    · refine ih (first+1) (by omega) ?_ ?_
      · intro index
        simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hinc index.succ
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using hback

theorem Certified.rows {program : Program} {base coefficient : Nat}
    (certificate : Certified program base coefficient) : Rows program base coefficient := by
  obtain ⟨hbound,hprefix,hinc,hback⟩ := certificate
  refine {
    pop := ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    restore := ⟨by omega, ?_, ?_, ?_⟩
    pair := ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    multiplyValid := by omega
    multiplyTest := ?_
    multiplyLoop := incrementTrace (base+21) (base+22) coefficient hbound hinc hback
  }
  · simpa [prefixRows] using hprefix 0
  · simpa [prefixRows] using hprefix 1
  · simpa [prefixRows] using hprefix 2
  · simpa [prefixRows] using hprefix 3
  · simpa [prefixRows] using hprefix 4
  · simpa [prefixRows] using hprefix 5
  · simpa [prefixRows] using hprefix 6
  · simpa [prefixRows] using hprefix 7
  · simpa [prefixRows] using hprefix 8
  · simpa [prefixRows] using hprefix 9
  · simpa [prefixRows] using hprefix 10
  · simpa [prefixRows] using hprefix 11
  · simpa [prefixRows] using hprefix 12
  · simpa [prefixRows] using hprefix 13
  · simpa [prefixRows] using hprefix 14
  · simpa [prefixRows] using hprefix 15
  · simpa [prefixRows] using hprefix 16
  · simpa [prefixRows] using hprefix 17
  · simpa [prefixRows] using hprefix 18
  · simpa [prefixRows] using hprefix 19
  · simpa [prefixRows] using hprefix 20
  · simpa [prefixRows] using hprefix 21

#print axioms Certified.rows

def expectedRow (base coefficient : Nat) (index : Fin (23+coefficient)) : Instruction :=
  if hi : index.val < 22 then
    prefixRows base coefficient ⟨index.val,hi⟩
  else if index.val < 22+coefficient then
    .inc 1 (some (base+index.val+1))
  else
    .jump (some (base+21))

/-- Compare each constructor as a consecutive source slice. A slice requires
    one traversal to its starting ordinal regardless of the number of rows. -/
def CertifiedSlice (program : Program) (base coefficient : Nat) : Prop :=
  base+22+coefficient < program.length ∧
    (program.drop base).take (23+coefficient) =
      List.ofFn (fun index => some (expectedRow base coefficient index))

instance (program : Program) (base coefficient : Nat) :
    Decidable (CertifiedSlice program base coefficient) := by
  unfold CertifiedSlice
  infer_instance

private theorem rowFromSlice {program : Program} {base coefficient : Nat}
    (hs : CertifiedSlice program base coefficient) (index : Fin (23+coefficient)) :
    row program (base+index.val) = some (expectedRow base coefficient index) := by
  have h := congrArg (fun xs : Program => xs[index.val]?) hs.2
  rw [List.getElem?_take_of_lt index.isLt,List.getElem?_drop,List.getElem?_ofFn] at h
  simp only [index.isLt,dif_pos] at h
  exact congrArg Option.join h

theorem CertifiedSlice.certified {program : Program} {base coefficient : Nat}
    (hs : CertifiedSlice program base coefficient) : Certified program base coefficient := by
  refine ⟨hs.1,?_,?_,?_⟩
  · intro index
    have h := rowFromSlice hs ⟨index.val,by have := index.isLt; omega⟩
    simpa [expectedRow,index.isLt] using h
  · intro index
    have h := rowFromSlice hs ⟨22+index.val,by have := index.isLt; omega⟩
    have h₁ : ¬22+index.val < 22 := by omega
    have h₂ : 22+index.val < 22+coefficient := by have := index.isLt; omega
    simpa [expectedRow,h₁,h₂,Nat.add_assoc] using h
  · have h := rowFromSlice hs ⟨22+coefficient,by omega⟩
    have h₁ : ¬22+coefficient < 22 := by omega
    simpa [expectedRow,h₁,Nat.add_assoc] using h

#print axioms CertifiedSlice.certified
end PA194ProgramCons
