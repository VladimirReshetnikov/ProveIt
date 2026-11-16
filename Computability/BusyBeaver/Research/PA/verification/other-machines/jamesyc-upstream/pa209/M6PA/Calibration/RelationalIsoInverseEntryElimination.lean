module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseEntry
@[expose] public section

/-! Finite two-coordinate elimination for an actual graph-object witness. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseEntryEliminate {Γ : List Form} (g n p : Nat) (q : Form)
    (h : ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar n) (.fvar p)))
    (k : ∀ {Δ : List Form}, (∀ x, x ∈ shifted (shifted Γ) → x ∈ Δ) →
      InverseEntryComponents Δ (g+1+1) (n+1+1) (p+1+1) 1 0 →
      ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim h
  let σ : Formula 1 := ∃¹ (mem (.fvar n) (.bvar 1) ⋏
    (edge (.fvar g) (.bvar 1) (.bvar 0) ⋏ kuratowski (.fvar p) (.bvar 0) (.bvar 1)))
  let C := σ.free :: shifted Γ
  let τ : Formula 1 := mem (.fvar (n+1)) (.fvar 0) ⋏
    (edge (.fvar (g+1)) (.fvar 0) (.bvar 0) ⋏ kuratowski (.fvar (p+1)) (.bvar 0) (.fvar 0))
  have ht : ND.Proof C (∃¹ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,τ] <;> inverseSyntax)
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D (mem (.fvar (n+1+1)) (.fvar 1) ⋏
      (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏ kuratowski (.fvar (p+1+1)) (.fvar 0) (.fvar 1))) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1 <;> (dsimp [τ] <;> inverseSyntax)
  have out := k (Δ := D) (by intro x hx; simp [D,C,shifted] at *; tauto)
    ⟨andLeft hd,andLeft (andRight hd),andRight (andRight hd)⟩
  convert out using 1 <;> (dsimp [D,C,σ,τ] <;> inverseSyntax)

#print axioms inverseEntryEliminate
end M6.PA.RelationalSource.PairGraph
