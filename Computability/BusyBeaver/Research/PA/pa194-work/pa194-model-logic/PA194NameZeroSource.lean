import PA194ForwardReflSuppliers
import PA194FoundationOrdinalInhabited
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194NameZeroSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open M6.PA.RelationalSource.Ordinal (Term Formula)
open PA194ForwardTyped

def nameZero : Proposition PA194PAeq.language := .exs (PA194PAeq.eq (.bvar 0) PA194PAeq.zero)
def target : Form := formula nameZero (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))

variable {Γ : List Form}
def zeroEqualityAt (a : Nat) (E : FormulaEquality Γ)
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar a))) :
    ND.Proof Γ (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))) := by
  let x : Term 0 := .fvar a
  let P : Formula 1 := ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let Q : Formula 1 := (Ordinal.domain (.fvar a) ⋏ eq (.fvar a) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.fvar a) (.bvar 0))
  have hbase : ND.Proof Γ ((Ordinal.domain x ⋏ eq x (.fvar a)) ⋏
      ((Ordinal.domain x ⋏ Ordinal.zero x) ⋏ orderIso x x)) :=
    ND.andIntro (ND.andIntro hd (E.reflexive x)) (ND.andIntro (ND.andIntro hd hz) hi)
  apply ND.exsIntro P x
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q x
    convert hbase using 1 <;> (dsimp [Q,x] <;> isoSyntax)
  convert hq using 1 <;> (dsimp [P,Q,x] <;> isoSyntax)

def proof (E : FormulaEquality Γ) (empty : ND.Proof Γ emptyFormula)
    (orderRefl : ND.Proof Γ orderIsoReflexivityStatement) : ND.Proof Γ target := by
  apply ND.exsElim empty
  let σ : Formula 1 := Ordinal.zero (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have hz : ND.Proof C (Ordinal.zero (.fvar 0)) := by
    have h : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have hd := Ordinal.zeroDomain (.fvar 0) hz
  have E' : FormulaEquality C := E.shifted.weaken (fun p hp => by simp [C,hp])
  have ho : ND.Proof C orderIsoReflexivityStatement := by
    have h := ND.shiftProof orderRefl
    have h' : ND.Proof C orderIsoReflexivityStatement.shift :=
      ND.weaken h (fun p hp => List.mem_cons_of_mem _ hp)
    convert h' using 1 <;> (try simp only [orderIsoReflexivityStatement] <;> isoSyntax)
  have hi : ND.Proof C (orderIso (.fvar 0) (.fvar 0)) := by
    have h := ND.allElim _ (.fvar 0) ho
    have hh : ND.Proof C (Ordinal.domain (.fvar 0) 🡒 orderIso (.fvar 0) (.fvar 0)) := by
      convert h using 1
      change _ = Semiformula.rewAux _ _
      simp only [Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux]
      all_goals isoSyntax
    exact ND.mp hd hh
  have he := zeroEqualityAt 0 E' hd hz hi
  let P : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.bvar 2)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0))))
  have hh : ND.Proof C (∃⁰ P) := by
    apply ND.exsIntro P (.fvar 0)
    convert ND.andIntro hd he using 1 <;> (dsimp [P] <;> isoSyntax)
  convert hh using 1 <;> (try simp only [target,nameZero,formula,PA194PAeq.eq,equal,value,bindEnv,shiftEnv] <;> isoSyntax)
  all_goals (dsimp [C,σ,Ordinal.zero]; rfl)

#print axioms proof
end PA194NameZeroSource
