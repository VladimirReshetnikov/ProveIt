import DiophantineConsistency.PellRepresentation
import DiophantineConsistency.DivisionRepresentation

/-!
# Explicit polynomial data for natural exponentiation

The finite Pell certificate is instantiated as supplied syntax. Truncated
subtraction uses its explicit graph representation. The correctness proof
uses `Pell.eq_pow_of_pell`, while all polynomial data are constructed directly.
-/

namespace DiophantineConsistency.PowerRepresentation

open PellRepresentation

variable {σ : Type*}

def modEqGraphs {f g h : (σ → ℕ) → ℕ}
    (rf : GraphRep f) (rg : GraphRep g) (rh : GraphRep h) :
    Rep σ (fun v => Nat.ModEq (h v) (f v) (g v)) := by
  let fs : Fin 3 → (σ → ℕ) → ℕ := ![f, g, h]
  let gs : ∀ i, GraphRep (fs i) := Fin.cases rf (Fin.cases rg (Fin.cases rh (fun i => Fin.elim0 i)))
  exact ((ArithmeticRep.modEq (0 : Fin 3) 1 2).compose gs).ofIff (fun _ => Iff.rfl)

/-- Inputs are output `m`, base `n`, exponent `k`; certificate coordinates are `w,a,t,z,x,y`. -/
abbrev CertificateVar := Fin 3 ⊕ Fin 6

def finiteCriterion (v : CertificateVar → ℕ) : Prop :=
  let m := v (.inl 0)
  let n := v (.inl 1)
  let k := v (.inl 2)
  let w := v (.inr 0)
  let a := v (.inr 1)
  let t := v (.inr 2)
  let z := v (.inr 3)
  let x := v (.inr 4)
  let y := v (.inr 5)
  (∃ ha : 1 < a, Pell.xn ha k = x ∧ Pell.yn ha k = y) ∧
    Nat.ModEq t x (y * (a - n) + m) ∧ 2 * a * n = t + (n * n + 1) ∧
    m < t ∧ n ≤ w ∧ k ≤ w ∧ norm (w + 1) a (w * z)

def finiteRep : Rep CertificateVar finiteCriterion := by
  let m : NatExpr CertificateVar := .var (.inl 0)
  let n : NatExpr CertificateVar := .var (.inl 1)
  let k : NatExpr CertificateVar := .var (.inl 2)
  let w : NatExpr CertificateVar := .var (.inr 0)
  let a : NatExpr CertificateVar := .var (.inr 1)
  let t : NatExpr CertificateVar := .var (.inr 2)
  let z : NatExpr CertificateVar := .var (.inr 3)
  let x : NatExpr CertificateVar := .var (.inr 4)
  let y : NatExpr CertificateVar := .var (.inr 5)
  let pellIndex : Fin 4 → CertificateVar := ![.inr 1, .inl 2, .inr 4, .inr 5]
  let pell := PellRepresentation.rep.reindex pellIndex
  let rhs := GraphRep.add (GraphRep.mul y.graphRep (GraphRep.sub a.graphRep n.graphRep)) m.graphRep
  let congruence := modEqGraphs x.graphRep rhs t.graphRep
  let normTerms : Fin 3 → NatExpr CertificateVar := ![w + 1, a, w * z]
  let last := (normRep (0 : Fin 3) 1 2).compose (fun i => (normTerms i).graphRep)
  let r := pell.conjunction (congruence.conjunction
    ((NaturalRelation.equality (2 * a * n) (t + (n * n + 1))).conjunction
    ((NaturalRelation.lt m t).conjunction
    ((NaturalRelation.le n w).conjunction
    ((NaturalRelation.le k w).conjunction last)))))
  exact r.ofIff (fun _ => Iff.rfl)

def criterion (v : Fin 3 → ℕ) : Prop :=
  v 2 = 0 ∧ v 0 = 1 ∨ 0 < v 2 ∧
    (v 1 = 0 ∧ v 0 = 0 ∨ 0 < v 1 ∧ ∃ w a t z x y : ℕ,
      finiteCriterion (Sum.elim v ![w, a, t, z, x, y]))

def criterionRep : Rep (Fin 3) criterion := by
  let m : NatExpr (Fin 3) := .var 0
  let n : NatExpr (Fin 3) := .var 1
  let k : NatExpr (Fin 3) := .var 2
  let zeroExponent := (NaturalRelation.equality k 0).conjunction (NaturalRelation.equality m 1)
  let zeroBase := (NaturalRelation.equality n 0).conjunction (NaturalRelation.equality m 0)
  let nontrivial := finiteRep.existsBlock
  let r := zeroExponent.disjunction ((NaturalRelation.lt 0 k).conjunction
    (zeroBase.disjunction ((NaturalRelation.lt 0 n).conjunction nontrivial)))
  refine r.ofIff ?_
  intro v
  change (v 2 = 0 ∧ v 0 = 1 ∨ 0 < v 2 ∧
    (v 1 = 0 ∧ v 0 = 0 ∨ 0 < v 1 ∧
      ∃ z : Fin 6 → ℕ, finiteCriterion (Sum.elim v z))) ↔ _
  apply or_congr Iff.rfl
  apply and_congr_right
  intro _
  apply or_congr Iff.rfl
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z 0, z 1, z 2, z 3, z 4, z 5, hz⟩
  · rintro ⟨w, a, t, z, x, y, h⟩
    exact ⟨![w, a, t, z, x, y], h⟩

theorem criterion_iff_pow (v : Fin 3 → ℕ) : criterion v ↔ v 1 ^ v 2 = v 0 := by
  rw [Pell.eq_pow_of_pell]
  unfold criterion
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hk
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hn
  constructor
  · rintro ⟨w, a, t, z, x, y, ⟨ha, hx, hy⟩, hc, he, hm, hnw, hkw, hnorm⟩
    change 1 < a at ha
    change v 1 ≤ w at hnw
    change Nat.ModEq t x (y * (a - v 1) + v 0) at hc
    change Pell.xn ha (v 2) = x at hx
    change Pell.yn ha (v 2) = y at hy
    have hw : 1 < w + 1 := by omega
    refine ⟨w, a, t, z, ha, ?_, he, hm, hnw, hkw, (norm_iff_nat hw).mp hnorm⟩
    rw [hx, hy]
    exact hc
  · rintro ⟨w, a, t, z, ha, hc, he, hm, hnw, hkw, hnorm⟩
    have hw : 1 < w + 1 := by omega
    exact ⟨w, a, t, z, Pell.xn ha (v 2), Pell.yn ha (v 2),
      ⟨ha, rfl, rfl⟩, hc, he, hm, hnw, hkw, (norm_iff_nat hw).mpr hnorm⟩

/-- Direct representation data for the output/base/exponent predicate. -/
def rep : Rep (Fin 3) (fun v => v 0 = v 1 ^ v 2) :=
  criterionRep.ofIff (fun v => (criterion_iff_pow v).trans eq_comm)

/-- A fixed finite graph representation of binary natural exponentiation. -/
def coordinates : GraphRep (fun v : Fin 2 → ℕ => v 0 ^ v 1) :=
  (rep.reindex (![none, some 0, some 1] : Fin 3 → Option (Fin 2))).ofIff
    (fun _ => Iff.rfl)

end DiophantineConsistency.PowerRepresentation

namespace DiophantineConsistency.GraphRep

/-- Explicit graph representations are closed under natural exponentiation. -/
def pow {σ : Type*} {f g : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    GraphRep (fun v => f v ^ g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose PowerRepresentation.coordinates arguments

end DiophantineConsistency.GraphRep

