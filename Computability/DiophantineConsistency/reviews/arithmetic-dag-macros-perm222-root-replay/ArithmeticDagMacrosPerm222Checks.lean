import BusyBeaver.ZFC.ArithmeticDagMacrosPerm222
set_option autoImplicit false
set_option Elab.async false
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagMacrosPerm222 ArithmeticCantor
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- All physical slots are stated explicitly, including the two scratch slots. -/
example (np tw ws ac p1 p2 s1 s2 pl : V) :
    enc (⟨np,tw,ws,ac,p1,p2,s1,s2,pl⟩ : AS V) =
      ArithmeticControlFile.fileValue ![ws,pl,tw,p1,ac,s2,np,p2,s1] := rfl

/-- Pairing requires no cleanliness premise, even with both input counters zero. -/
example (st : AS V) : Rn (.node 162) {st with s1:=0,tw:=0} {st with s1:=0,tw:=0} := by
  simpa [cantor, triangle] using pair162 ({st with s1:=0,tw:=0} : AS V)

/-- Zero input preserves arbitrary preexisting scratch values in the unpair walk. -/
example (st : AS V) : Rn (.node 115) {st with pl:=0} {st with pl:=0} := by
  simpa [unpairAS, AS.withPLZero] using loop115 ({st with pl:=0} : AS V)
example (st : AS V) : Rn (.node 116) {st with ws:=0} {st with ws:=0} := by
  simpa [unpairAS, AS.withWSZero] using loop116 ({st with ws:=0} : AS V)

/-- Reads add to dirty destinations; only the scratch pair is clean. -/
example (np tw ws ac d h raw : V) :
    Rn (.node 175) (⟨np,tw,ws,ac,d,h,0,0,raw⟩ : AS V)
      (⟨np,tw,ws,ac,d+first raw,h,0,0,second raw⟩ : AS V) :=
  read_p1 _ ⟨rfl,rfl⟩

/-- Empty stack is permitted by total Cantor projections. -/
example (st : AS V) (hc : Clean st) :
    Rn (.node 119) {st with ws:=0} {st with ws:=0,tw:=ArithmeticCode254.wim 0 st.tw} := by
  have hz : cantor (0 : V) 0 = 0 := by simp [cantor, triangle]
  have hfirst : first (0 : V) = 0 := by simpa only [hz] using first_cantor (0 : V) 0
  have hsecond : second (0 : V) = 0 := by simpa only [hz] using second_cantor (0 : V) 0
  simpa only [hfirst, hsecond] using cons ({st with ws:=0} : AS V) hc

/-- Both fetch cases include raw candidate zero and preserve arbitrary work data. -/
example (st : AS V) : Rn (.node 133) {st with pl:=1} {st with pl:=0} := by
  simpa using fetch_pos ({st with pl:=1} : AS V) 0 (by simp)
example (st : AS V) :
    Rn (.node 133) {st with pl:=0,s1:=0}
      {st with pl:=st.np,np:=st.np+1,s1:=0} := fetch_zero _ rfl rfl

#print axioms ArithmeticDagMacrosPerm222.lreg_enc
#print axioms ArithmeticDagMacrosPerm222.lupd_enc
#print axioms ArithmeticDagMacrosPerm222.pair162
#print axioms ArithmeticDagMacrosPerm222.loop136
#print axioms ArithmeticDagMacrosPerm222.loop115
#print axioms ArithmeticDagMacrosPerm222.loop116
#print axioms ArithmeticDagMacrosPerm222.read_ac
#print axioms ArithmeticDagMacrosPerm222.read_p1
#print axioms ArithmeticDagMacrosPerm222.read_p2
#print axioms ArithmeticDagMacrosPerm222.pushwff
#print axioms ArithmeticDagMacrosPerm222.par1
#print axioms ArithmeticDagMacrosPerm222.par2
#print axioms ArithmeticDagMacrosPerm222.par3
#print axioms ArithmeticDagMacrosPerm222.cons
#print axioms ArithmeticDagMacrosPerm222.wel_m
#print axioms ArithmeticDagMacrosPerm222.wal_m
#print axioms ArithmeticDagMacrosPerm222.weq_m
#print axioms ArithmeticDagMacrosPerm222.wn_m
#print axioms ArithmeticDagMacrosPerm222.wa_m
#print axioms ArithmeticDagMacrosPerm222.wex_m
#print axioms ArithmeticDagMacrosPerm222.fetch_pos
#print axioms ArithmeticDagMacrosPerm222.fetch_zero
end SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222Checks
