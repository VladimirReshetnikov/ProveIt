import Mathlib

/-!
UNCOMPILED BLUEPRINT -- Lean 4.32.0 / mathlib v4.32.0.
This file specifies finite objects and records of outstanding proof obligations.
No record below has been instantiated. There is no claimed main-theorem proof.
Ordinary Lean specifications are separate from derivations in embedded iPRA.
-/

namespace HurwitzKhinchinIPRA

structure RatInterval where
  lo : ℚ
  hi : ℚ

def span (I : RatInterval) : ℚ := I.hi - I.lo
def properUnit (I : RatInterval) : Prop :=
  0 ≤ I.lo ∧ I.lo < I.hi ∧ I.hi ≤ 1
def endpoints : List RatInterval → List ℚ
  | [] => []
  | I :: rest => I.lo :: I.hi :: endpoints rest

/-- Finite content; endpoint membership has no effect on cell lengths. -/
def unionLength (intervals : List RatInterval) : ℚ :=
  let es := (endpoints intervals).mergeSort (fun x y => decide (x ≤ y))
  (es.zip es.tail).foldl (fun acc ab =>
    if (intervals.any (fun I => decide (I.lo ≤ ab.1 ∧ ab.2 ≤ I.hi))) = true
    then acc + (ab.2 - ab.1) else acc) 0

def dyadicError (s : ℕ) : ℚ := (1 / 2 : ℚ) ^ s
def hurwitzPolynomial (p : ℤ) (q : ℕ) (x : ℚ) : ℚ :=
  5 * (q : ℚ)^2 * ((q : ℚ) * x - (p : ℚ))^2

/-- Endpoint checks imply the strict sharp inequality throughout the box. -/
structure HurwitzCertificate (B : ℕ) where
  p : ℤ
  q : ℕ
  large : B < q
  coprime : Nat.Coprime p.natAbs q
  box : RatInterval
  ordered : box.lo ≤ box.hi
  margin : ℚ
  margin_pos : 0 < margin
  left_check : hurwitzPolynomial p q box.lo ≤ 1 - margin
  right_check : hurwitzPolynomial p q box.hi ≤ 1 - margin

/-- The separation field supplies a finite, positive rational-apartness check. -/
structure IrrationalName where
  approx : ℕ → ℚ
  coherent : ∀ i j, |approx i - approx j| ≤ dyadicError i + dyadicError j
  sep : ℤ → ℕ → ℕ
  apart : ∀ p q, 0 < q →
    2 * dyadicError (sep p q) < |approx (sep p q) - (p : ℚ) / (q : ℚ)|

/- This pointwise apartness interface converts to the manuscript's uniform
denominator modulus by a bounded maximum over q <= Q and bounded numerators.
An a priori bound on |x| comes from |approx 0| + 2. PR coding of the functions
and the proof of this conversion remain separate obligations. -/

/-- Outstanding productive Hurwitz objective; PR status is a separate task. -/
structure HurwitzExtraction (a : IrrationalName) where
  stage : ℕ → ℕ
  certificate : (B : ℕ) → HurwitzCertificate B
  encloses : ∀ B,
    (certificate B).box.lo ≤ a.approx (stage B) - dyadicError (stage B) ∧
    a.approx (stage B) + dyadicError (stage B) ≤ (certificate B).box.hi

def nonnegative (psi : ℕ → ℚ) : Prop := ∀ q, 0 < q → 0 ≤ psi q
def nonincreasing (psi : ℕ → ℚ) : Prop := ∀ q, 0 < q → psi (q+1) ≤ psi q
def divergenceWitness (psi : ℕ → ℚ) (D : ℕ → ℕ) : Prop :=
  ∀ n, 0 < n → n ≤ D n ∧
    1 ≤ ((List.range (D n + 1 - n)).map (fun i => psi (n+i))).sum

/-- Deterministic finite enumeration; pairs are (numerator, denominator). -/
def centers (J : RatInterval) (k : ℕ) : List (ℕ × ℕ) :=
  let Q := 2^k
  (List.range (Q+1)).flatMap (fun q =>
    ((List.range (q+1)).filter (fun p => decide
      (Q / 4 < q ∧ Nat.Coprime p q ∧
       J.lo + span J / 4 < (p : ℚ) / (q : ℚ) ∧
       (p : ℚ) / (q : ℚ) < J.hi - span J / 4))).map (fun p => (p,q)))

def mass (psi : ℕ → ℚ) (k : ℕ) : ℚ := min ((2 : ℚ)^k * psi (2^k)) 1
def radius (psi : ℕ → ℚ) (k : ℕ) : ℚ := mass psi k / (8 * (4 : ℚ)^k)
def scaleIntervals (psi : ℕ → ℚ) (J : RatInterval) (k : ℕ) :
    List RatInterval :=
  (centers J k).map (fun pq =>
    let x := (pq.1 : ℚ) / (pq.2 : ℚ)
    ⟨x - radius psi k, x + radius psi k⟩)
def blockIntervals (psi : ℕ → ℚ) (J : RatInterval) (K b : ℕ) :
    List RatInterval :=
  (List.range (b+1-K)).flatMap (fun i => scaleIntervals psi J (K+i))
def blockMass (psi : ℕ → ℚ) (K b : ℕ) : ℚ :=
  ((List.range (b+1-K)).map (fun i => mass psi (K+i))).sum

def approximationIntervals (psi : ℕ → ℚ) (N M : ℕ) : List RatInterval :=
  (List.range (M+1-N)).flatMap (fun i =>
    let q := N+i
    (List.range (q+1)).map (fun p =>
      let x := (p : ℚ) / (q : ℚ)
      let r := psi q / (q : ℚ)
      ⟨max 0 (x-r), min 1 (x+r)⟩))

/-- These are tasks to prove, not additional axioms or available lemmas. -/
structure FiniteKernelObligations where
  interval_subadditivity : ∀ Is,
    unionLength Is ≤ (Is.map (fun I => max 0 (span I))).sum
  certificate_valid : ∀ B (c : HurwitzCertificate B) x,
    c.box.lo ≤ x → x ≤ c.box.hi → hurwitzPolynomial c.p c.q x < 1
  denominator_count : ∀ J k, properUnit J → 512 ≤ k →
    512 ≤ (k : ℚ) * span J →
    span J * (4 : ℚ)^k / 32 ≤ ((centers J k).length : ℚ) ∧
    ((centers J k).length : ℚ) ≤ span J * (4 : ℚ)^k
  local_coverage : ∀ psi J K b, nonnegative psi → properUnit J →
    512 ≤ K → 512 ≤ (K : ℚ) * span J → K ≤ b →
    1 ≤ blockMass psi K b →
    span J / 16384 ≤ unionLength (blockIntervals psi J K b)
  finite_convergence : ∀ psi N M, nonnegative psi → 0 < N →
    unionLength (approximationIntervals psi N M) ≤
      4 * ((List.range (M+1-N)).map (fun i => psi (N+i))).sum

/-- Fixed-round residual-gap construction must supply this record. -/
structure CoverageObligations (psi : ℕ → ℚ) (D : ℕ → ℕ) where
  cutoff : ℕ → ℕ → ℕ
  cutoff_ge : ∀ N m, N ≤ cutoff N m
  coverage : ∀ N m, 0 < N → nonnegative psi → nonincreasing psi →
    divergenceWitness psi D →
    1 - dyadicError m ≤ unionLength (approximationIntervals psi N (cutoff N m))

/-- Prototype only: prove its specification before using bounded induction. -/
def allBelow (P : ℕ → Bool) (n : ℕ) : Bool := (List.range n).all P

/-
Remaining milestones:
(1) Instantiate the finite obligation records and HurwitzExtraction.
(2) Give syntactic PR codes for fixed input functions and every construction.
(3) Build actual Prf PRAAx derivations using proved bounded-fold reflection.
(4) In a ProveIt module, apply LeanProofs.ConciseIPRA.pra_iff_native.
The repository bridge does not turn arbitrary Lean proofs into iPRA proofs.
-/

end HurwitzKhinchinIPRA

