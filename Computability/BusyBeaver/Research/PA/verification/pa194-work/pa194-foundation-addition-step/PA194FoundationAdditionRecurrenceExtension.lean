import PA194FoundationAdditionRecurrence

/-! The actual successor step for addition recurrence. New predecessor cases
are discharged by local ordinal predecessor uniqueness, not extensionality. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

structure RecurrenceInputs (Γ : List Form) (top u c v g h : Nat) where
  topDomain : ND.Proof Γ (Ordinal.domain (.fvar u))
  inputSucc : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u))
  outputSucc : ND.Proof Γ (Ordinal.successor (.fvar c) (.fvar v))
  endpoint : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c))
  extension : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))
  recurrence : ND.Proof Γ (addRecurrence (.fvar g))

def RecurrenceInputs.weaken {Γ Δ} {top u c v g h : Nat}
    (I : RecurrenceInputs Γ top u c v g h) (inc : ∀ p, p ∈ Γ → p ∈ Δ) :
    RecurrenceInputs Δ top u c v g h where
  topDomain := ND.weaken I.topDomain inc
  inputSucc := ND.weaken I.inputSucc inc
  outputSucc := ND.weaken I.outputSucc inc
  endpoint := ND.weaken I.endpoint inc
  extension := ND.weaken I.extension inc
  recurrence := ND.weaken I.recurrence inc

def edgeShift {Γ : List Form} (g x y : Nat) (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar (y+1))) := by
  convert shiftProof he using 1 ; traceSyntax

def recurrenceShift {Γ : List Form} (g : Nat) (hr : ND.Proof Γ (addRecurrence (.fvar g))) :
    ND.Proof (shifted Γ) (addRecurrence (.fvar (g+1))) := by
  convert shiftProof hr using 1 ; addSyntax

def RecurrenceInputs.shift {Γ} {top u c v g h : Nat} (I : RecurrenceInputs Γ top u c v g h) :
    RecurrenceInputs (shifted Γ) (top+1) (u+1) (c+1) (v+1) (g+1) (h+1) where
  topDomain := domainShift u I.topDomain
  inputSucc := Ordinal.successorShift top u I.inputSucc
  outputSucc := Ordinal.successorShift c v I.outputSucc
  endpoint := edgeShift g top c I.endpoint
  extension := exactShift g h u v I.extension
  recurrence := recurrenceShift g I.recurrence

def newRecurrenceCase {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h x y z : Nat) (I : RecurrenceInputs Γ top u c v g h)
    (hxu : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (hyv : ND.Proof Γ (eq (.fvar y) (.fvar v)))
    (hzx : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (addPrevious (.fvar h) (.fvar z) (.fvar y)) := by
  have hzu := successorTargetTransport E z x u hxu hzx
  have hzt := successorPredecessorUnique E.core u z top I.topDomain hzu I.inputSucc
  have he := edgeInputTransport E g top z c (E.symmetryOf hzt) I.endpoint
  have hh := exactPreservesEdge g h u v z c I.extension he
  have hs := successorTargetTransport E c v y (E.symmetryOf hyv) I.outputSucc
  exact previousIntro h z y c hh hs

def recurrenceExtensionAt {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h x y z : Nat) (I : RecurrenceInputs Γ top u c v g h)
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (addPrevious (.fvar h) (.fvar z) (.fvar y)) := by
  have hc := mp he (andLeft (exactAt g h u v x y I.extension))
  apply orElim hc
  · let q : Form := edge (.fvar g) (.fvar x) (.fvar y)
    have prev := recurrenceAt g x y z (up I.recurrence q) (assumption (by simp [q])) (up hs q)
    exact preservePrevious g h u v z y (up I.extension q) prev
  · let q : Form := eq (.fvar x) (.fvar u) ⋏ eq (.fvar y) (.fvar v)
    have hp : ND.Proof (q::Γ) q := assumption (by simp)
    let inc : ∀ p, p ∈ Γ → p ∈ q::Γ := fun p hp => List.mem_cons_of_mem q hp
    exact newRecurrenceCase (E.weaken inc) top u c v g h x y z (I.weaken inc)
      (andLeft hp) (andRight hp) (up hs q)

def recurrenceExtension {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h : Nat) (I : RecurrenceInputs Γ top u c v g h) :
    ND.Proof Γ (addRecurrence (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have III := I.shift.shift.shift
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (addPrevious (.fvar (h+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::shifted (shifted (shifted Γ))) q := assumption (by simp)
    let inc := fun p (hp : p ∈ shifted (shifted (shifted Γ))) => List.mem_cons_of_mem q hp
    exact recurrenceExtensionAt (E.shifted.shifted.shifted.weaken inc)
      (top+1+1+1) (u+1+1+1) (c+1+1+1) (v+1+1+1) (g+1+1+1) (h+1+1+1) 2 1 0
      (III.weaken inc) (andLeft hp) (andRight hp)
  convert result using 1 ; previousSyntax

#print axioms newRecurrenceCase
#print axioms recurrenceExtensionAt
#print axioms recurrenceExtension
end M6.PA.RelationalSource.PairGraph
