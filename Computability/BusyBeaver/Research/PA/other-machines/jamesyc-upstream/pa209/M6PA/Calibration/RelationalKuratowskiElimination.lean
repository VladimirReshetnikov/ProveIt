module
public import M6PA.Theory
public import M6PA.Calibration.RelationalKuratowskiComponents
@[expose] public section

/-! Explicit two-witness elimination for raw Kuratowski syntax. The continuation
receives actual finite components and only ordinary context weakening. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def Components.weaken {Γ Δ : List Form} {p a b s t : Nat}
    (h : Components Γ p a b s t) (incl : ∀ x, x ∈ Γ → x ∈ Δ) : Components Δ p a b s t where
  single := ND.weaken h.single incl
  inner := ND.weaken h.inner incl
  outer := ND.weaken h.outer incl

def Components.shift {Γ : List Form} {p a b s t : Nat}
    (h : Components Γ p a b s t) : Components (shifted Γ) (p+1) (a+1) (b+1) (s+1) (t+1) where
  single := singletonShift a s h.single
  inner := pairShift a b t h.inner
  outer := pairShift s t p h.outer

def eliminate {Γ : List Form} (p a b : Nat) (q : Form)
    (hk : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (k : ∀ {Δ : List Form}, (∀ x, x ∈ shifted (shifted Γ) → x ∈ Δ) →
      Components Δ (p+1+1) (a+1+1) (b+1+1) 1 0 →
      ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim hk
  let σ : Formula 1 := ∃¹ (singleton (.fvar a) (.bvar 1) ⋏
    (pair (.fvar a) (.fvar b) (.bvar 0) ⋏ pair (.bvar 1) (.bvar 0) (.fvar p)))
  let C := σ.free :: shifted Γ
  let τ : Formula 1 := singleton (.fvar (a+1)) (.fvar 0) ⋏
    (pair (.fvar (a+1)) (.fvar (b+1)) (.bvar 0) ⋏
      pair (.fvar 0) (.bvar 0) (.fvar (p+1)))
  have ht : ND.Proof C (∃¹ τ) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ,τ] ; graphSyntax
  apply exsElim ht
  let D := τ.free :: shifted C
  have hc : ND.Proof D (singleton (.fvar (a+1+1)) (.fvar 1) ⋏
    (pair (.fvar (a+1+1)) (.fvar (b+1+1)) (.fvar 0) ⋏
      pair (.fvar 1) (.fvar 0) (.fvar (p+1+1)))) := by
    have h : ND.Proof D τ.free := assumption (by simp [D])
    convert h using 1 ; dsimp [τ] ; graphSyntax
  have hd := k (Δ := D) (by intro x hx; simp [D,C,shifted] at *; tauto)
    ⟨andLeft hc, andLeft (andRight hc), andRight (andRight hc)⟩
  convert hd using 1 <;> (dsimp [D,C,σ,τ] <;> graphSyntax)

#print axioms eliminate
end M6.PA.RelationalSource.PairGraph

