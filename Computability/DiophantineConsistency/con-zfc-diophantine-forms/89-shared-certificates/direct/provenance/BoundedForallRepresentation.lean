import DiophantineConsistency.BoundedForallCertificate
import DiophantineConsistency.FactorialRepresentation

/-!
# Supplied representation data for bounded universal quantification

The CRT certificate is compiled from its natural expression inputs. Polynomial
interpretation occurs only in the correctness proof; the expression and witness
count are supplied by the representation constructors.
-/

namespace DiophantineConsistency.BoundedForallRepresentation

open Nat Finset
open scoped Vector3

variable {σ : Type} {m : ℕ}

/-- Parameters, coordinate bounds, encoded coordinates, and one encoded index. -/
abbrev CertificateVar (σ : Type) (m : ℕ) := ((σ ⊕ Fin m) ⊕ Fin m) ⊕ Fin 1

def parameter (i : σ) : CertificateVar σ m := .inl (.inl (.inl i))
def upper (i : Fin m) : CertificateVar σ m := .inl (.inl (.inr i))
def encoded (i : Fin m) : CertificateVar σ m := .inl (.inr i)
def index : CertificateVar σ m := .inr 0

/-- Evaluate at the external bound and at the coordinatewise witness bounds. -/
def upperMap (b : σ) : Option σ ⊕ Fin m → CertificateVar σ m
  | .inl none => parameter b
  | .inl (some i) => parameter i
  | .inr i => upper i

/-- Evaluate at the encoded index and encoded witness coordinates. -/
def encodedMap : Option σ ⊕ Fin m → CertificateVar σ m
  | .inl none => index
  | .inl (some i) => parameter i
  | .inr i => encoded i

@[simp] theorem upperMap_assignment (b : σ) (x : σ → ℕ) (u a : Fin m → ℕ)
    (c : Fin 1 → ℕ) :
    Sum.elim (Sum.elim (Sum.elim x u) a) c ∘ upperMap b =
      Sum.elim (Option.elim' (x b) x) u := by
  funext j
  rcases j with k | i
  · cases k <;> rfl
  · rfl

@[simp] theorem encodedMap_assignment (x : σ → ℕ) (u a : Fin m → ℕ)
    (c : Fin 1 → ℕ) :
    Sum.elim (Sum.elim (Sum.elim x u) a) c ∘ encodedMap =
      Sum.elim (Option.elim' (c 0) x) a := by
  funext j
  rcases j with k | i
  · cases k <;> rfl
  · rfl

/-- A representation of the explicit arithmetic formula for the CRT product. -/
def productGraph {τ : Type*} {n t : (τ → ℕ) → ℕ}
    (rn : GraphRep n) (rt : GraphRep t) :
    GraphRep (fun v => MRDP.encodedModuliProduct (n v) (t v)) := by
  let q := ((((rn.add (GraphRep.constant 1)).mul rt).add
    (GraphRep.constant 1)).pow rn).add (GraphRep.constant 2)
  exact ((rt.pow rn).mul (rn.factorial.mul ((q.add rn).binomial rn))).mod
    ((rt.mul q).sub (GraphRep.constant 1))

private def dvdGraphs {τ : Type*} {f g : (τ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : Rep τ (fun v => f v ∣ g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact (Rep.compose (ArithmeticRep.dvd (0 : Fin 2) 1) arguments).ofIff
    (fun _ => Iff.rfl)

/-- The factorial scale, computed from the supplied natural expressions. -/
def scale (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ)
    (v : CertificateVar σ m → ℕ) : ℕ :=
  (e.eval (v ∘ upperMap b) + f.eval (v ∘ upperMap b) + v (parameter b)).factorial

/-- The finite certificate uses falling factorials expressed by binomial coefficients. -/
def finiteCriterion (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ)
    (v : CertificateVar σ m → ℕ) : Prop :=
  let T := scale e f b v
  let B := MRDP.encodedModuliProduct (v (parameter b)) T
  (∀ i : Fin m, B ∣ (v (upper i) + 1).factorial *
    (v (encoded i)).choose (v (upper i) + 1)) ∧
  Nat.ModEq B (MRDP.crtModulus T (v index)) 0 ∧
  Nat.ModEq B (e.eval (v ∘ encodedMap)) (f.eval (v ∘ encodedMap))

/-- Supplied syntax for every arithmetic condition in the CRT certificate. -/
def finiteRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    Rep (CertificateVar σ m) (finiteCriterion e f b) := by
  let n : GraphRep (fun v : CertificateVar σ m → ℕ => v (parameter b)) :=
    GraphRep.coordinate (parameter b)
  let t := (((e.graphRep.reindex (upperMap b)).add
    (f.graphRep.reindex (upperMap b))).add n).factorial
  let B := productGraph n t
  let coordinateConditions := Rep.allFin m
    (fun i v => MRDP.encodedModuliProduct (v (parameter b)) (scale e f b v) ∣
      (v (upper i) + 1).factorial * (v (encoded i)).choose (v (upper i) + 1))
    (fun i =>
      let u := (GraphRep.coordinate (upper i)).add (GraphRep.constant 1)
      dvdGraphs B (u.factorial.mul ((GraphRep.coordinate (encoded i)).binomial u)))
  let indexCondition := PowerRepresentation.modEqGraphs
    ((((GraphRep.coordinate index).add (GraphRep.constant 1)).mul t).add
      (GraphRep.constant 1)) (GraphRep.constant 0) B
  let evaluationCondition := PowerRepresentation.modEqGraphs
    (e.graphRep.reindex encodedMap) (f.graphRep.reindex encodedMap) B
  exact (coordinateConditions.conjunction
    (indexCondition.conjunction evaluationCondition)).ofIff (fun _ => Iff.rfl)

/-- All certificate coordinates are explicit finite existential blocks. -/
def certificateRep (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    Rep σ (fun x => ∃ u a : Fin m → ℕ, ∃ c : Fin 1 → ℕ,
      finiteCriterion e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) :=
  (finiteRep e f b).existsBlock.existsBlock.existsBlock

/-- Correctness of the supplied finite certificate, using the checked CRT theorem. -/
theorem certificate_iff (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) (x : σ → ℕ) :
    (∃ u a : Fin m → ℕ, ∃ c : Fin 1 → ℕ,
      finiteCriterion e f b (Sum.elim (Sum.elim (Sum.elim x u) a) c)) ↔
    ∀ k < x b, ∃ w : Fin m → ℕ,
      e.eval (Sum.elim (Option.elim' k x) w) =
        f.eval (Sum.elim (Option.elim' k x) w) := by
  have h := boundedForallCertificate e.toPolynomial f.toPolynomial (x b) x
  simp only [MvPolynomial.eval_add, NatExpr.eval_toPolynomial] at h
  constructor
  · rintro ⟨u, a, c, hc⟩
    apply h.mp
    refine ⟨u, a, [c 0], ?_⟩
    simpa only [finiteCriterion, scale, upperMap_assignment, encodedMap_assignment,
      parameter, upper, encoded, index, Sum.elim_inl, Sum.elim_inr,
      Option.elim'_none, Option.elim'_some, Vector3.head, Vector3.cons_fz,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose] using hc
  · intro hk
    obtain ⟨u, a, c, hc⟩ := h.mpr hk
    refine ⟨u, a, fun _ => c.head, ?_⟩
    simpa only [finiteCriterion, scale, upperMap_assignment, encodedMap_assignment,
      parameter, upper, encoded, index, Sum.elim_inl, Sum.elim_inr,
      Option.elim'_none, Option.elim'_some,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose] using hc

/-- Compile the bounded family from its supplied pair of natural expressions. -/
def representation (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) :
    Rep σ (fun x => ∀ k < x b, ∃ w : Fin m → ℕ,
      e.eval (Sum.elim (Option.elim' k x) w) =
        f.eval (Sum.elim (Option.elim' k x) w)) :=
  (certificateRep e f b).ofIff (certificate_iff e f b)

end DiophantineConsistency.BoundedForallRepresentation

namespace DiophantineConsistency.Rep

variable {σ : Type} {P : (Option σ → ℕ) → Prop}

/-- Explicit representations are closed under an input-bounded universal quantifier. -/
def boundedForall (r : Rep (Option σ) P) (b : σ) :
    Rep σ (fun x => ∀ k < x b, P (Option.elim' k x)) :=
  (BoundedForallRepresentation.representation r.expression.splitNatural.1
    r.expression.splitNatural.2 b).ofIff (fun x =>
      forall_congr' (fun k => imp_congr_right (fun _ =>
        (r.correct_splitNatural (Option.elim' k x)).symm)))

end DiophantineConsistency.Rep

