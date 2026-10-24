import DiophantineConsistency.NaturalExpression
import DiophantineConsistency.ComposeRepresentation
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Data.Fin.VecNotation

/-!
# Explicit representation data for the Pell-coordinate graph

The supplied expression is assembled from the finite Matiyasevic certificate.
No polynomial is selected from `Dioph`, `IsPoly`, or an existential theorem.
All represented inputs and witnesses are natural numbers, while the norm
residual is evaluated with ordinary integer subtraction.
-/

namespace DiophantineConsistency.PellRepresentation

variable {σ : Type*}

def norm (a x y : ℕ) : Prop :=
  (x : ℤ) * x - ((a : ℤ) * a - 1) * y * y = 1

private theorem sub_eq_one (m n : ℕ) : m - n = 1 ↔ (m : ℤ) - n = 1 := by omega

theorem norm_iff_nat {a x y : ℕ} (ha : 1 < a) :
    norm a x y ↔ x * x - (a * a - 1) * y * y = 1 := by
  have hsq : 1 ≤ a * a := by nlinarith
  rw [sub_eq_one]
  simp only [Int.natCast_mul, Int.natCast_sub hsq, Int.natCast_one, norm]

def normRep (a x y : σ) : Rep σ (fun v => norm (v a) (v x) (v y)) :=
  (Rep.equality
    (Expr.var x * Expr.var x - (Expr.var a * Expr.var a - 1) * Expr.var y * Expr.var y)
    1).ofIff (fun _ => Iff.rfl)

namespace NaturalRelation

def equality (p q : NatExpr σ) : Rep σ (fun v => p.eval v = q.eval v) := by
  let terms : Fin 2 → NatExpr σ := ![p, q]
  let r : Rep (Fin 2) (fun v => v 0 = v 1) :=
    (Rep.equality (Expr.var (0 : Fin 2)) (Expr.var 1)).ofIff
    (fun v => by simp only [Expr.eval_var, Int.natCast_inj])
  exact (r.compose (fun i => (terms i).graphRep)).ofIff (fun _ => Iff.rfl)

def le (p q : NatExpr σ) : Rep σ (fun v => p.eval v ≤ q.eval v) := by
  let terms : Fin 2 → NatExpr σ := ![p, q]
  exact ((ArithmeticRep.le (0 : Fin 2) 1).compose
    (fun i => (terms i).graphRep)).ofIff (fun _ => Iff.rfl)

def lt (p q : NatExpr σ) : Rep σ (fun v => p.eval v < q.eval v) := by
  let terms : Fin 2 → NatExpr σ := ![p, q]
  exact ((ArithmeticRep.lt (0 : Fin 2) 1).compose
    (fun i => (terms i).graphRep)).ofIff (fun _ => Iff.rfl)

def dvd (p q : NatExpr σ) : Rep σ (fun v => p.eval v ∣ q.eval v) := by
  let terms : Fin 2 → NatExpr σ := ![p, q]
  exact ((ArithmeticRep.dvd (0 : Fin 2) 1).compose
    (fun i => (terms i).graphRep)).ofIff (fun _ => Iff.rfl)

def modEq (p q modulus : NatExpr σ) :
    Rep σ (fun v => Nat.ModEq (modulus.eval v) (p.eval v) (q.eval v)) := by
  let terms : Fin 3 → NatExpr σ := ![p, q, modulus]
  exact ((ArithmeticRep.modEq (0 : Fin 3) 1 2).compose
    (fun i => (terms i).graphRep)).ofIff (fun _ => Iff.rfl)

end NaturalRelation

/-- Four input coordinates are `a,n,x,y`; five certificate coordinates are `u,w,s,t,b`. -/
abbrev CertificateVar := Fin 4 ⊕ Fin 5

def finiteCriterion (v : CertificateVar → ℕ) : Prop :=
  let a := v (.inl 0)
  let n := v (.inl 1)
  let x := v (.inl 2)
  let y := v (.inl 3)
  let u := v (.inr 0)
  let w := v (.inr 1)
  let s := v (.inr 2)
  let t := v (.inr 3)
  let b := v (.inr 4)
  norm a x y ∧ norm a u w ∧ norm b s t ∧ 1 < b ∧
    Nat.ModEq (4 * y) b 1 ∧ Nat.ModEq u b a ∧ 0 < w ∧ y * y ∣ w ∧
    Nat.ModEq u s x ∧ Nat.ModEq (4 * y) t n

/-- The certificate is compiled from explicit equality, arithmetic and finite conjunction data. -/
def finiteRep : Rep CertificateVar finiteCriterion := by
  let a : NatExpr CertificateVar := .var (.inl 0)
  let n : NatExpr CertificateVar := .var (.inl 1)
  let x : NatExpr CertificateVar := .var (.inl 2)
  let y : NatExpr CertificateVar := .var (.inl 3)
  let u : NatExpr CertificateVar := .var (.inr 0)
  let w : NatExpr CertificateVar := .var (.inr 1)
  let s : NatExpr CertificateVar := .var (.inr 2)
  let t : NatExpr CertificateVar := .var (.inr 3)
  let b : NatExpr CertificateVar := .var (.inr 4)
  let r := (normRep (.inl 0) (.inl 2) (.inl 3)).conjunction
    ((normRep (.inl 0) (.inr 0) (.inr 1)).conjunction
    ((normRep (.inr 4) (.inr 2) (.inr 3)).conjunction
    ((NaturalRelation.lt 1 b).conjunction
    ((NaturalRelation.modEq b 1 (4 * y)).conjunction
    ((NaturalRelation.modEq b a u).conjunction
    ((NaturalRelation.lt 0 w).conjunction
    ((NaturalRelation.dvd (y * y) w).conjunction
    ((NaturalRelation.modEq s x u).conjunction
      (NaturalRelation.modEq t n (4 * y))))))))))
  exact r.ofIff (fun _ => Iff.rfl)

def criterion (v : Fin 4 → ℕ) : Prop :=
  1 < v 0 ∧ v 1 ≤ v 3 ∧
    (v 2 = 1 ∧ v 3 = 0 ∨ ∃ u w s t b : ℕ,
      finiteCriterion (Sum.elim v ![u, w, s, t, b]))

def criterionRep : Rep (Fin 4) criterion := by
  let a : NatExpr (Fin 4) := .var 0
  let n : NatExpr (Fin 4) := .var 1
  let x : NatExpr (Fin 4) := .var 2
  let y : NatExpr (Fin 4) := .var 3
  let nontrivial := finiteRep.existsBlock
  let base := (NaturalRelation.equality x 1).conjunction (NaturalRelation.equality y 0)
  let r := (NaturalRelation.lt 1 a).conjunction
    ((NaturalRelation.le n y).conjunction (base.disjunction nontrivial))
  refine r.ofIff ?_
  intro v
  change (1 < v 0 ∧ v 1 ≤ v 3 ∧ ((v 2 = 1 ∧ v 3 = 0) ∨
    ∃ z : Fin 5 → ℕ, finiteCriterion (Sum.elim v z))) ↔ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z 0, z 1, z 2, z 3, z 4, hz⟩
  · rintro ⟨u, w, s, t, b, h⟩
    exact ⟨![u, w, s, t, b], h⟩

theorem criterion_iff_pell (v : Fin 4 → ℕ) :
    criterion v ↔ ∃ ha : 1 < v 0, Pell.xn ha (v 1) = v 2 ∧ Pell.yn ha (v 1) = v 3 := by
  rw [Pell.matiyasevic]
  constructor
  · rintro ⟨ha, hn, hbase | ⟨u, w, s, t, b, hx, hu, hs, hb, hrest⟩⟩
    · exact ⟨ha, hn, Or.inl hbase⟩
    · exact ⟨ha, hn, Or.inr ⟨u, w, s, t, b,
        (norm_iff_nat ha).mp hx, (norm_iff_nat ha).mp hu, (norm_iff_nat hb).mp hs, hb, hrest⟩⟩
  · rintro ⟨ha, hn, hbase | ⟨u, w, s, t, b, hx, hu, hs, hb, hrest⟩⟩
    · exact ⟨ha, hn, Or.inl hbase⟩
    · exact ⟨ha, hn, Or.inr ⟨u, w, s, t, b,
        (norm_iff_nat ha).mpr hx, (norm_iff_nat ha).mpr hu, (norm_iff_nat hb).mpr hs, hb, hrest⟩⟩

/-- Executable polynomial and witness-count data for both Pell coordinates. -/
def rep : Rep (Fin 4) (fun v =>
    ∃ ha : 1 < v 0, Pell.xn ha (v 1) = v 2 ∧ Pell.yn ha (v 1) = v 3) :=
  criterionRep.ofIff criterion_iff_pell

end DiophantineConsistency.PellRepresentation

