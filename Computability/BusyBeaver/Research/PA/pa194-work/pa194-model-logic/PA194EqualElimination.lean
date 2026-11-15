import PA194InverseEqualIntro
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194InverseEqual
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

structure EqualComponents (Γ : List Form) (a b x y : Nat) where
  left : ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ eq (.fvar x) (.fvar a))
  right : ND.Proof Γ (Ordinal.domain (.fvar y) ⋏ eq (.fvar y) (.fvar b))
  iso : ND.Proof Γ (orderIso (.fvar x) (.fvar y))

def equalEliminate (a b : Nat) (q : Form) (h : ND.Proof Γ (equalAt a b))
    (k : ∀ {Δ : List Form}, (∀ x, x ∈ shifted (shifted Γ) → x ∈ Δ) →
      EqualComponents Δ (a+1+1) (b+1+1) 1 0 → ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim h
  let σ : Ordinal.Formula 1 := ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let C := σ.free :: shifted Γ
  let τ : Ordinal.Formula 1 := (Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (a+1))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar (b+1))) ⋏ orderIso (.fvar 0) (.bvar 0))
  have ht : ND.Proof C (∃⁰ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1
    simp [σ,τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D ((Ordinal.domain (.fvar 1) ⋏ eq (.fvar 1) (.fvar (a+1+1))) ⋏
      ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (b+1+1))) ⋏ orderIso (.fvar 1) (.fvar 0))) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1
    simp [τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
  exact k (Δ := D) (by intro x hx; simp [D,C,shifted] at *; tauto)
    ⟨andLeft hd,andLeft (andRight hd),andRight (andRight hd)⟩
#print axioms equalEliminate
end PA194InverseEqual
