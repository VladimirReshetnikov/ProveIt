module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAxioms
public import Foundation.FirstOrder.LK.Basic
@[expose] public section

/-! A constructive natural-deduction interface whose values ARE Foundation
LK.Derivation. No new unverified calculus, validity premise, or completeness
choice is introduced. This is the arithmetic-language instance of the previously checked local ND interface. It supports finite arithmetic certificate templates. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

deriving instance DecidableEq for Func
deriving instance DecidableEq for Rel
instance : language.DecidableEq where
  func k := inferInstanceAs (DecidableEq (Func k))
  rel k := inferInstanceAs (DecidableEq (Rel k))

namespace ND
abbrev Form := Proposition language

def negatives (Γ : List Form) : Multiset Form := (Γ.map Semiformula.neg : Multiset Form)
@[simp] theorem negatives_cons (p : Form) (Γ : List Form) : negatives (p::Γ) = negatives Γ + ⦃∼p⦄ := by
  change ∼p ::ₘ negatives Γ = _
  exact (Multiset.add_atom_eq_cons _ _).symm

def traversal (Γ : List Form) : (negatives Γ).Traversal := Multiset.Traversal.ofList _

abbrev Proof (Γ : List Form) (p : Form) := LK.Derivation (negatives Γ + ⦃p⦄)

def assumption {Γ : List Form} {p : Form} (h : p ∈ Γ) : Proof Γ p :=
  (LK.Derivation.eta p).contra ((traversal Γ).succ p) (by
    intro q hq
    simp only [Multiset.mem_add, Multiset.mem_atom_iff] at hq
    rcases hq with rfl | rfl
    · simp
    · simp only [Multiset.mem_add, negatives, Multiset.mem_coe, List.mem_map, Multiset.mem_atom_iff]
      exact Or.inl ⟨p,h,rfl⟩)

def weaken {Γ Δ : List Form} {p : Form} (d : Proof Γ p) (h : ∀ q,q ∈ Γ → q ∈ Δ) : Proof Δ p :=
  d.contra ((traversal Δ).succ p) (by
    intro q hq
    simp only [Multiset.mem_add] at hq ⊢
    rcases hq with hq | hq
    · left
      simp only [negatives,Multiset.mem_coe,List.mem_map] at hq ⊢
      rcases hq with ⟨r,hr,he⟩
      exact ⟨r,h r hr,he⟩
    · exact Or.inr hq)

def closed {Γ : List Form} {p : Form} (d : LK.Derivation ⦃p⦄) : Proof Γ p :=
  (Structural.weakenMany (traversal Γ) d).cast (by abel)

def mp {Γ : List Form} {p q : Form} (d : Proof Γ p) (e : Proof Γ (p 🡒 q)) : Proof Γ q :=
  (OneSidedLK.modusPonens e d).contra ((traversal Γ).succ q) (by intro x hx; simpa using hx)

def impIntro {Γ : List Form} {p q : Form} (d : Proof (p::Γ) q) : Proof Γ (p 🡒 q) :=
  (LK.Derivation.or (Γ := negatives Γ) (φ := ∼p) (ψ := q)
    (d.cast (by simp only [negatives_cons, Semiformula.neg_eq, Semiformula.neg_neg]; abel)))

def andIntro {Γ : List Form} {p q : Form} (d : Proof Γ p) (e : Proof Γ q) : Proof Γ (p ⋏ q) :=
  LK.Derivation.and d e

def andLeft {Γ : List Form} {p q : Form} (d : Proof Γ (p ⋏ q)) : Proof Γ p :=
  mp d (closed (OneSidedLK.AxiomDerivation.and₁ p q))
def andRight {Γ : List Form} {p q : Form} (d : Proof Γ (p ⋏ q)) : Proof Γ q :=
  mp d (closed (OneSidedLK.AxiomDerivation.and₂ p q))
def orLeft {Γ : List Form} {p q : Form} (d : Proof Γ p) : Proof Γ (p ⋎ q) :=
  mp d (closed (OneSidedLK.AxiomDerivation.or₁ p q))
def orRight {Γ : List Form} {p q : Form} (d : Proof Γ q) : Proof Γ (p ⋎ q) :=
  mp d (closed (OneSidedLK.AxiomDerivation.or₂ p q))

def botElim {Γ : List Form} {p : Form} (d : Proof Γ ⊥) : Proof Γ p :=
  (OneSidedLK.removeBot d).weakening

def contradiction {Γ : List Form} {p : Form} (d : Proof Γ p) (e : Proof Γ (∼p)) : Proof Γ ⊥ :=
  ((LK.Derivation.cut d e).weakening (φ := ⊥)).contra ((traversal Γ).succ ⊥) (by intro x hx; simpa using hx)

def byContradiction {Γ : List Form} {p : Form} (d : Proof (∼p::Γ) ⊥) : Proof Γ p :=
  (OneSidedLK.removeBot d).cast (by simp only [negatives_cons, Semiformula.neg_eq, Semiformula.neg_neg])

def orElim {Γ : List Form} {p q r : Form} (d : Proof Γ (p ⋎ q))
    (dp : Proof (p::Γ) r) (dq : Proof (q::Γ) r) : Proof Γ r := by
  let hp : LK.Derivation ((negatives Γ + ⦃r⦄) + ⦃∼p⦄) := dp.cast (by simp only [negatives_cons, Semiformula.neg_eq, Semiformula.neg_neg]; abel)
  let hq : LK.Derivation ((negatives Γ + ⦃r⦄) + ⦃∼q⦄) := dq.cast (by simp only [negatives_cons, Semiformula.neg_eq, Semiformula.neg_neg]; abel)
  let hn : LK.Derivation ((negatives Γ + ⦃r⦄) + ⦃∼(p ⋎ q)⦄) :=
    (LK.Derivation.and hp hq).cast (by simp)
  exact (LK.Derivation.cut d hn).contra ((traversal Γ).succ r) (by intro x hx; simpa using hx)

def shifted (Γ : List Form) := Γ.map Semiformula.shift

theorem negatives_shifted (Γ : List Form) : negatives (shifted Γ) = Rewriting.shifts (negatives Γ) := by
  simp [negatives,shifted,Rewriting.shifts,Multiset.map_coe,List.map_map,Function.comp_def, Semiformula.shift, ← Semiformula.neg_eq]

def allIntro {Γ : List Form} {p : Semiproposition language 1}
    (d : Proof (shifted Γ) p.free) : Proof Γ (∀¹ p) :=
  LK.Derivation.all (d.cast (by rw [negatives_shifted]))

def allElim {Γ : List Form} (p : Semiproposition language 1) (t : Semiterm language Nat 0)
    (d : Proof Γ (∀¹ p)) : Proof Γ (p/[t]) := by
  let hi : LK.Derivation (⦃p/[t]⦄ + ⦃(∼p)/[t]⦄) :=
    (LK.Derivation.eta (p/[t])).cast (by simp)
  let hn : LK.Derivation (⦃p/[t]⦄ + ⦃∼(∀¹ p)⦄) :=
    (LK.Derivation.exs (φ := ∼p) (t := t) hi).cast (by simp)
  exact (LK.Derivation.cut d hn).cast (by simp)

def exsIntro {Γ : List Form} (p : Semiproposition language 1) (t : Semiterm language Nat 0)
    (d : Proof Γ (p/[t])) : Proof Γ (∃¹ p) := LK.Derivation.exs d

def exsElim {Γ : List Form} {p : Semiproposition language 1} {q : Form}
    (d : Proof Γ (∃¹ p)) (e : Proof (p.free :: shifted Γ) q.shift) : Proof Γ q := by
  let he : LK.Derivation (Rewriting.shifts (negatives Γ + ⦃q⦄) + ⦃(∼p).free⦄) :=
    e.cast (by simp only [negatives_cons, negatives_shifted]; simp [Rewriting.shifts]; abel)
  let hn : LK.Derivation ((negatives Γ + ⦃q⦄) + ⦃∼(∃¹ p)⦄) :=
    (LK.Derivation.all he).cast (by simp)
  exact (LK.Derivation.cut d hn).contra ((traversal Γ).succ q) (by intro x hx; simpa using hx)

def shiftProof {Γ : List Form} {p : Form} (d : Proof Γ p) : Proof (shifted Γ) p.shift :=
  d.shift.cast (by simp [negatives_shifted,Rewriting.shifts])

#print axioms mp
#print axioms allElim
#print axioms exsElim
end ND
end M6.PA.Presentation

