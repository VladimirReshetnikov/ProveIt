import DiophantineConsistency.ExpressionSize
import DiophantineConsistency.BoundedForallRepresentation
import DiophantineConsistency.DirectComposition

/-! # Witness-count metadata for the explicit bounded-universal compiler -/

namespace DiophantineConsistency.BoundedForallSize

open scoped BigOperators

def addCost (a b : ℕ) : ℕ := a + b + 2
def mulCost (a b : ℕ) : ℕ := a + b + 2
def subCost (a b : ℕ) : ℕ := 3 + GraphRep.subCoordinates.witnessCount + a + b
def modCost (a b : ℕ) : ℕ := 3 + GraphRep.modCoordinates.witnessCount + a + b
def powCost (a b : ℕ) : ℕ := 3 + PowerRepresentation.coordinates.witnessCount + a + b
def binomialCost (a b : ℕ) : ℕ :=
  3 + FactorialRepresentation.binomialCoordinates.witnessCount + a + b
def factorialCost (a : ℕ) : ℕ := 2 + FactorialRepresentation.factorialCoordinates.witnessCount + a

@[simp] theorem constant_count {σ : Type*} (n : ℕ) :
    (GraphRep.constant (σ := σ) n).witnessCount = 0 := rfl
@[simp] theorem coordinate_count {σ : Type*} (i : σ) :
    (GraphRep.coordinate i).witnessCount = 0 := rfl
@[simp] theorem reindex_count {σ τ : Type*} {f : (σ → ℕ) → ℕ}
    (r : GraphRep f) (h : σ → τ) : (r.reindex h).witnessCount = r.witnessCount := rfl

@[simp] theorem add_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.add s).witnessCount = addCost r.witnessCount s.witnessCount :=
  ExpressionSize.graphAdd_witnessCount r s
@[simp] theorem mul_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.mul s).witnessCount = mulCost r.witnessCount s.witnessCount :=
  ExpressionSize.graphMul_witnessCount r s

theorem predicate_compose_count {σ : Type*} {n : ℕ} {P : (Fin n → ℕ) → Prop}
    {f : Fin n → (σ → ℕ) → ℕ} (r : Rep (Fin n) P) (s : ∀ i, GraphRep (f i)) :
    (r.compose s).witnessCount = n + (r.witnessCount + ∑ i, (s i).witnessCount) := by
  simp only [Rep.compose, Rep.ofIff, Rep.existsBlock, Rep.conjunction, Rep.reindex,
    Rep.allFin_witnessCount]

@[simp] theorem sub_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.sub s).witnessCount = subCost r.witnessCount s.witnessCount := by
  simp only [GraphRep.sub, GraphRep.compose_witnessCount, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_zero]
  simp [subCost, Nat.add_assoc]

@[simp] theorem mod_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.mod s).witnessCount = modCost r.witnessCount s.witnessCount := by
  simp only [GraphRep.mod, GraphRep.compose_witnessCount, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_zero]
  simp [modCost, Nat.add_assoc]

@[simp] theorem pow_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.pow s).witnessCount = powCost r.witnessCount s.witnessCount := by
  simp only [GraphRep.pow, GraphRep.compose_witnessCount, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_zero]
  simp [powCost, Nat.add_assoc]

@[simp] theorem binomial_count {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.binomial s).witnessCount = binomialCost r.witnessCount s.witnessCount := by
  simp only [GraphRep.binomial, GraphRep.compose_witnessCount, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_zero]
  simp [binomialCost, Nat.add_assoc]

@[simp] theorem factorial_count {σ : Type*} {f : (σ → ℕ) → ℕ}
    (r : GraphRep f) : (r.factorial).witnessCount = factorialCost r.witnessCount := by
  simp only [GraphRep.factorial, GraphRep.compose_witnessCount, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp [factorialCost, Nat.add_assoc]

@[simp] theorem modEq_count {σ : Type*} {f g h : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) :
    (PowerRepresentation.modEqGraphs r s t).witnessCount =
      5 + r.witnessCount + s.witnessCount + t.witnessCount := by
  change 3 + (2 + (r.witnessCount + (s.witnessCount + (t.witnessCount + 0)))) = _
  omega

def productCost (n t : ℕ) : ℕ :=
  let q := addCost (powCost (addCost (mulCost (addCost n 0) t) 0) n) 0
  modCost (mulCost (powCost t n) (mulCost (factorialCost n) (binomialCost (addCost q n) n)))
    (subCost (mulCost t q) 0)

@[simp] theorem product_count {σ : Type*} {n t : (σ → ℕ) → ℕ}
    (rn : GraphRep n) (rt : GraphRep t) :
    (BoundedForallRepresentation.productGraph rn rt).witnessCount =
      productCost rn.witnessCount rt.witnessCount := by
  simp only [BoundedForallRepresentation.productGraph, add_count, mul_count,
    pow_count, factorial_count, binomial_count, mod_count, sub_count, constant_count]
  rfl

def scaleCost (p q : ℕ) : ℕ := factorialCost (addCost (addCost p q) 0)
def modulusCost (p q : ℕ) : ℕ := productCost 0 (scaleCost p q)
def coordinateCost (p q : ℕ) : ℕ :=
  3 + modulusCost p q + mulCost (factorialCost (addCost 0 0)) (binomialCost 0 (addCost 0 0))
def indexCost (p q : ℕ) : ℕ :=
  5 + addCost (mulCost (addCost 0 0) (scaleCost p q)) 0 + modulusCost p q
def evaluationCost (p q : ℕ) : ℕ := 5 + p + q + modulusCost p q
def certificateCost (m p q : ℕ) : ℕ :=
  m + m + 1 + (m * coordinateCost p q + (indexCost p q + evaluationCost p q))

theorem finiteRep_count {σ : Type} {m : ℕ} (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    (BoundedForallRepresentation.finiteRep e f b).witnessCount =
      m * coordinateCost e.graphRep.witnessCount f.graphRep.witnessCount +
        (indexCost e.graphRep.witnessCount f.graphRep.witnessCount +
          evaluationCost e.graphRep.witnessCount f.graphRep.witnessCount) := by
  let n : GraphRep (fun v : BoundedForallRepresentation.CertificateVar σ m → ℕ =>
      v (BoundedForallRepresentation.parameter b)) :=
    GraphRep.coordinate (BoundedForallRepresentation.parameter b)
  let t := (((e.graphRep.reindex (BoundedForallRepresentation.upperMap b)).add
    (f.graphRep.reindex (BoundedForallRepresentation.upperMap b))).add n).factorial
  let B := BoundedForallRepresentation.productGraph n t
  simp only [BoundedForallRepresentation.finiteRep, Rep.ofIff, Rep.conjunction,
    Rep.allFin_witnessCount,
    coordinate_count, constant_count, reindex_count,
    add_count, mul_count, factorial_count,
    product_count, modEq_count]
  simp [coordinateCost, indexCost, evaluationCost, modulusCost, scaleCost,
    Nat.add_assoc]
  calc
    _ = ∑ _i : Fin m,
        (3 + modulusCost e.graphRep.witnessCount f.graphRep.witnessCount +
          mulCost (factorialCost (addCost 0 0)) (binomialCost 0 (addCost 0 0))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      let u : GraphRep (fun v : BoundedForallRepresentation.CertificateVar σ m → ℕ =>
          v (BoundedForallRepresentation.upper i) + 1) :=
        (GraphRep.coordinate (BoundedForallRepresentation.upper i)).add (GraphRep.constant 1)
      let rhs := u.factorial.mul
        ((GraphRep.coordinate (BoundedForallRepresentation.encoded i)).binomial u)
      change 2 + (1 + (B.witnessCount + (rhs.witnessCount + 0))) = _
      simp only [B, t, n, rhs, u, product_count, reindex_count,
        coordinate_count, constant_count, add_count, mul_count,
        factorial_count, binomial_count]
      simp [modulusCost, scaleCost, Nat.add_assoc]
      omega
    _ = _ := by simp [modulusCost, scaleCost, Nat.add_assoc]

theorem certificate_count {σ : Type} {m : ℕ} (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    (BoundedForallRepresentation.certificateRep e f b).witnessCount =
      certificateCost m e.graphRep.witnessCount f.graphRep.witnessCount := by
  simp only [BoundedForallRepresentation.certificateRep, Rep.existsBlock,
    finiteRep_count]
  simp [certificateCost, Nat.add_assoc]

theorem boundedForall_count {σ : Type} {P : (Option σ → ℕ) → Prop}
    (r : Rep (Option σ) P) (b : σ) :
    (r.boundedForall b).witnessCount = certificateCost r.witnessCount
      ((ExpressionSize.splitSize r.expression).positive - 1)
      ((ExpressionSize.splitSize r.expression).negative - 1) := by
  change (BoundedForallRepresentation.certificateRep
    r.expression.splitNatural.1 r.expression.splitNatural.2 b).witnessCount = _
  rw [certificate_count]
  have hp := ExpressionSize.natGraph_witnessCount r.expression.splitNatural.1
  have hn := ExpressionSize.natGraph_witnessCount r.expression.splitNatural.2
  rw [(ExpressionSize.splitSize_correct r.expression).1] at hp
  rw [(ExpressionSize.splitSize_correct r.expression).2] at hn
  have hpe : r.expression.splitNatural.1.graphRep.witnessCount =
      (ExpressionSize.splitSize r.expression).positive - 1 := by omega
  have hne : r.expression.splitNatural.2.graphRep.witnessCount =
      (ExpressionSize.splitSize r.expression).negative - 1 := by omega
  rw [hpe, hne]

#print axioms boundedForall_count

end DiophantineConsistency.BoundedForallSize
