import PA194EqualElimination
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194EqualZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194InverseEqual
variable {Γ Δ : List Form}

def equalZeroAt (a : Nat) : Form := ∃⁰ ∃⁰
  ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))

theorem equalZeroAt_shift (a : Nat) : (equalZeroAt a).shift = equalZeroAt (a+1) := by
  change Semiformula.rewAux Rew.shift (equalZeroAt a) = _
  simp [equalZeroAt,Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,Rew.shift,Rew.map,Rew.q]

structure Components (Γ : List Form) (a x y : Nat) where
  left : ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ eq (.fvar x) (.fvar a))
  zero : ND.Proof Γ (Ordinal.zero (.fvar y))
  iso : ND.Proof Γ (orderIso (.fvar x) (.fvar y))

def Components.weaken {a x y : Nat} (h : Components Γ a x y)
    (hincl : ∀ p, p ∈ Γ → p ∈ Δ) : Components Δ a x y :=
  ⟨ND.weaken h.left hincl,ND.weaken h.zero hincl,ND.weaken h.iso hincl⟩

def Components.shift {a x y : Nat} (h : Components Γ a x y) :
    Components (ND.shifted Γ) (a+1) (x+1) (y+1) := by
  refine ⟨?_,?_,?_⟩
  · have hh := ND.shiftProof h.left
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [Semiformula.rewAux,domain_rew,eq,Rew.shift,Rew.map]
  · exact Ordinal.zeroShift y h.zero
  · have hh := ND.shiftProof h.iso
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [orderIso_rew,Rew.shift,Rew.map]

def eliminate (a : Nat) (q : Form) (h : ND.Proof Γ (equalZeroAt a))
    (k : ∀ {Δ : List Form}, (∀ x, x ∈ shifted (shifted Γ) → x ∈ Δ) →
      Components Δ (a+1+1) 1 0 → ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim h
  let σ : Ordinal.Formula 1 := ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let C := σ.free :: shifted Γ
  let τ : Ordinal.Formula 1 := (Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (a+1))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.fvar 0) (.bvar 0))
  have ht : ND.Proof C (∃⁰ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1
    simp [σ,τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,Rew.free,Rew.q]
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D ((Ordinal.domain (.fvar 1) ⋏ eq (.fvar 1) (.fvar (a+1+1))) ⋏
      ((Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)) ⋏ orderIso (.fvar 1) (.fvar 0))) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1
    simp [τ,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,Rew.free,Rew.q]
  exact k (Δ := D) (by intro x hx; simp [D,C,shifted] at *; tauto)
    ⟨andLeft hd,andRight (andLeft (andRight hd)),andRight (andRight hd)⟩
#print axioms equalZeroAt_shift
#print axioms Components.shift
#print axioms eliminate
end PA194EqualZero
