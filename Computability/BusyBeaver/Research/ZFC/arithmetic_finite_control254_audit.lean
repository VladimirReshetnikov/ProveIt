import BusyBeaver.ZFC.ArithmeticFiniteControl254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticFiniteControl254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.binaryTerm_val
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.binaryValue_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.lookup_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.lookup_supported
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.lookup_absent
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.binaryValue_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.bitsPrefix_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteControl254.start_fixed_frame

section Open
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (bs : List Bool) : (binaryTerm bs).val (![] : Fin 0 → V) = binaryValue bs :=
  binaryTerm_val bs
example (bs : List Bool) : binaryValue (V := V) bs =
    (ArithmeticMachinePerm252.bitsCode bs : V) := binaryValue_cast bs
example (rows : List Row) (out q branch : V) :
    (lookupDef rows).val.Evalb ![out,q,branch] ↔ out = lookupValue rows q branch := by simp
example (rows : List Row) (q branch : V) (h : lookupValue rows q branch ≠ 0) :
    ∃ row ∈ rows, q = binaryValue row.key := by
  obtain ⟨row,hr,hkey,_⟩ := lookup_supported rows q branch h
  exact ⟨row,hr,hkey⟩
example (rows : List Row) (q branch : V)
    (h : ∀ row ∈ rows, q ≠ binaryValue row.key) : lookupValue rows q branch = 0 :=
  lookup_absent rows q branch h
example (branch : V) :
    lookupValue [⟨[true],[false,false,true],[false,false,true]⟩]
      (binaryValue [true]) branch = binaryValue [false,false,true] := by
  by_cases hb : branch = 0 <;> simp [lookupValue,hb]
example : binaryValue (V := V) [false,false,false] = 0 := by simp [binaryValue]
end Open

section Induction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (bs : List Bool) : binaryValue (V := V) bs =
    ArithmeticSiteBootPerm252.bitsPrefix bs 0 := binaryValue_prefix bs
example (bs : List Bool) (suffix : V) :
    ArithmeticSiteBootPerm252.bitsPrefix bs suffix =
      ArithmeticSiteBootPerm252.bitsPrefix bs 0 +
        ArithmeticMachineUniformScansPerm252.bitPrefix false (bs.length : V) suffix :=
  bitsPrefix_split bs suffix
example (P : List Bool) (hP : P.length ≤ 40) (values : List V) (count gap : V) :
    ArithmeticSitePerm252.startValue values count gap P =
      frameValue (binaryValue P) values count gap := start_fixed_frame P hP values count gap
example (values : List V) (count gap : V) :
    ArithmeticSitePerm252.startValue values count gap [false,false,false] =
      frameValue 0 values count gap := by
  simpa [binaryValue] using start_fixed_frame [false,false,false] (by decide) values count gap
end Induction

/-- Actual maximum finite PC-code witness from the separate Python table.
These two controls test compact syntax, without unfolding a huge unary numeral. -/
def maxPC : List Bool :=
  [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true]
example : ArithmeticMachinePerm252.bitsCode maxPC = 15952311447 := by decide
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] :
    (binaryTerm maxPC).val (![] : Fin 0 → V) =
      (ArithmeticMachinePerm252.bitsCode maxPC : V) :=
  (binaryTerm_val maxPC).trans (binaryValue_cast maxPC)
