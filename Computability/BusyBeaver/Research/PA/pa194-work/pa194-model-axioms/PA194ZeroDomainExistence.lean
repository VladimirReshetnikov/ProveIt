import PA194FoundationOrdinalInhabited
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ZeroDomainExistence
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND

def zeroExists : Form := ∃⁰ (domain (.bvar 0) ⋏ zero (.bvar 0))

def proof {Γ : List Form} (d : ND.Proof Γ emptyFormula) : ND.Proof Γ zeroExists := by
  apply exsElim d
  let σ : Formula 1 := zero (.bvar 0)
  let C := σ.free :: shifted Γ
  have hz : ND.Proof C (zero (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have hd := zeroDomain (.fvar 0) hz
  apply exsIntro _ (.fvar 0)
  convert andIntro hd hz using 1 <;> (try simp only [zeroExists]) <;> ordinalSyntax

def derivation : LO.FirstOrder.Derivation ([emptyFormula].map Semiformula.neg ++ [zeroExists]) :=
  (proof (Γ := [emptyFormula]) (assumption (by simp))).contra (by simp [ND.Proof])
#print axioms proof
#print axioms derivation
end PA194ZeroDomainExistence
