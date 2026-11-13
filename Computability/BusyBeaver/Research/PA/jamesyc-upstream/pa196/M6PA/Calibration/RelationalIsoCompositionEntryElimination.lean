module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEntry
@[expose] public section

/-! Three eigenvariables expose the actual composition object coordinates. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionEntryEliminate {Γ : List Form} (g h n p : Nat) (q : Form)
    (he : ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar n) (.fvar p)))
    (k : ∀ {Δ : List Form}, (∀ r, r ∈ shifted (shifted (shifted Γ)) → r ∈ Δ) →
      CompositionEntryComponents Δ (g+1+1+1) (h+1+1+1) (n+1+1+1) (p+1+1+1) 2 1 0 →
      ND.Proof Δ q.shift.shift.shift) : ND.Proof Γ q := by
  apply exsElim he
  let σ : Formula 1 := ∃¹ ∃¹ (mem (.fvar n) (.bvar 2) ⋏
    (edge (.fvar g) (.bvar 2) (.bvar 1) ⋏
      (edge (.fvar h) (.bvar 1) (.bvar 0) ⋏ kuratowski (.fvar p) (.bvar 2) (.bvar 0))))
  let C := σ.free :: shifted Γ
  let τ : Formula 1 := ∃¹ (mem (.fvar (n+1)) (.fvar 0) ⋏
    (edge (.fvar (g+1)) (.fvar 0) (.bvar 1) ⋏
      (edge (.fvar (h+1)) (.bvar 1) (.bvar 0) ⋏ kuratowski (.fvar (p+1)) (.fvar 0) (.bvar 0))))
  have ht : ND.Proof C (∃¹ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,τ] <;> compositionSyntax)
  apply exsElim ht
  let D := τ.free :: shifted C
  let υ : Formula 1 := mem (.fvar (n+1+1)) (.fvar 1) ⋏
    (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏
      (edge (.fvar (h+1+1)) (.fvar 0) (.bvar 0) ⋏ kuratowski (.fvar (p+1+1)) (.fvar 1) (.bvar 0)))
  have hu : ND.Proof D (∃¹ υ) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1 <;> (dsimp [τ,υ] <;> compositionSyntax)
  apply exsElim hu
  let F := υ.free :: shifted D
  have hh : ND.Proof F (mem (.fvar (n+1+1+1)) (.fvar 2) ⋏
      (edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        (edge (.fvar (h+1+1+1)) (.fvar 1) (.fvar 0) ⋏ kuratowski (.fvar (p+1+1+1)) (.fvar 2) (.fvar 0)))) := by
    have hh : ND.Proof F υ.free := assumption (by simp [F])
    convert hh using 1 <;> (dsimp [υ] <;> compositionSyntax)
  have out := k (Δ := F) (by intro r hr; simp [F,D,C,shifted] at *; tauto)
    ⟨andLeft hh,andLeft (andRight hh),andLeft (andRight (andRight hh)),andRight (andRight (andRight hh))⟩
  convert out using 1 <;> (dsimp [F,D,C,σ,τ,υ] <;> compositionSyntax)

#print axioms compositionEntryEliminate
end M6.PA.RelationalSource.PairGraph
