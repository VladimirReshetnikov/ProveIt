import PA194SuccEqualSyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

structure SuccEqualComponents (Γ : List Form) (a b x y : Nat) where
  left : ND.Proof Γ (succValue a x)
  right : ND.Proof Γ (succValue b y)
  iso : ND.Proof Γ (orderIso (.fvar x) (.fvar y))

def succEqualEliminate (a b : Nat) (q : Form) (h : ND.Proof Γ (succEqualAt a b))
    (k : ∀ {Δ : List Form}, (∀ x, x ∈ shifted (shifted Γ) → x ∈ Δ) →
      SuccEqualComponents Δ (a+1+1) (b+1+1) 1 0 → ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim h
  let σ : Ordinal.Formula 1 := ∃⁰ (succValueTerm (.fvar a) (.bvar 1) ⋏
    (succValueTerm (.fvar b) (.bvar 0) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let C := σ.free :: shifted Γ
  let τ : Ordinal.Formula 1 := succValueTerm (.fvar (a+1)) (.fvar 0) ⋏
    (succValueTerm (.fvar (b+1)) (.bvar 0) ⋏ orderIso (.fvar 0) (.bvar 0))
  have ht : ND.Proof C (∃⁰ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1
    simp [σ,τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,succValueTerm_rew,succValueTerm_fvar,orderIso_rew,Rew.free,Rew.q]
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D (succValue (a+1+1) 1 ⋏
      (succValue (b+1+1) 0 ⋏ orderIso (.fvar 1) (.fvar 0))) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1
    simp [τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,succValueTerm_rew,succValueTerm_fvar,orderIso_rew,Rew.free,Rew.q]
  exact k (Δ := D) (by intro x hx; simp [D,C,shifted] at *; tauto)
    ⟨andLeft hd,andLeft (andRight hd),andRight (andRight hd)⟩
#print axioms succEqualEliminate
end PA194SuccInjective
