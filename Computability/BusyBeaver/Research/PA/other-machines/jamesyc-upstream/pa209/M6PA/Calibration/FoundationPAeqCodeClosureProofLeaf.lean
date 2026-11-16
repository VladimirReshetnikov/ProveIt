module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeCanonicalInduction
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language
local notation "U" => Presentation.ordinaryPAeq

theorem canonicalSuccessorAxiom_provable {q : V} (hq : IsUFormula PAeq q)
    (hs : shift PAeq q=q) : Provable U (canonicalSuccessorAxiom q) := by
  have hb : IsSemiformula PAeq (0+matrixParameterCount q) (canonicalSuccessorBody q) := by
    simpa [canonicalSuccessorBody] using closedSuccessorBody_valid (matrixParameterCount_valid hq)
  have ha : IsFormula PAeq (canonicalSuccessorAxiom q) := hb.qqAlls
  apply Derivable.toProvable
  exact Derivable.by_axm (by simp [ha]) _ (by simp) (canonicalSuccessorAxiom_mem hq hs)

theorem provable_all_iff_free {p : V} (hp : IsSemiformula PAeq 1 p) :
    Provable U (qqAll p) ↔ Provable U (Bootstrapping.free PAeq p) := by
  let p' : Bootstrapping.Semiformula V PAeq 1 := ⟨p,by simpa using hp⟩
  constructor
  · intro h
    have h' : (U).internalize V ⊢ ∀¹p' := (tprovable_iff_provable (T:=U)).mpr h
    have hs' : (U).internalize V ⊢ ∀¹p'.shift := by simpa using TProof.shift! h'
    have hf := TProof.specialize! hs'
      (Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V PAeq)
    have hf' : (U).internalize V ⊢ p'.free := by
      simpa [Bootstrapping.Semiformula.free] using hf
    exact (tprovable_iff_provable (T:=U)).mp hf'
  · intro h
    have h' : (U).internalize V ⊢ p'.free := (tprovable_iff_provable (T:=U)).mpr h
    exact (tprovable_iff_provable (T:=U)).mp (TProof.all! h')

#print axioms canonicalSuccessorAxiom_provable
#print axioms provable_all_iff_free
end M6.PA.FoundationPAeqCode

