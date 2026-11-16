import SeriesTargets

/-!
# Simple-root chart producer: concrete definitions and UNPROVED targets

This module supplies the Gaussian-rational representation missing from the
real-rational `SeriesTargets` prototype.  All computations use Nat, Rat,
finite coefficient lists and explicitly indexed samples.  The named targets
below are definitions of type `Prop`, NOT asserted theorems.  No new axiom
or admitted proof is used.

`CoeffNames` and `GName` are host-Lean parameters used to describe schemas
for fixed primitive recursive evaluators.  This file does not assert that
every Lean function is PR, and does not quantify over arbitrary function
objects in the intended first-order iPRA formula.
-/

namespace IPRAFramework.ChartProducer

open IPRAFramework.Series (qabs dyadic)

structure Gaussian where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

def gzero : Gaussian := ⟨0, 0⟩
def gone : Gaussian := ⟨1, 0⟩
def gadd (z w : Gaussian) : Gaussian := ⟨z.re + w.re, z.im + w.im⟩
def gneg (z : Gaussian) : Gaussian := ⟨-z.re, -z.im⟩
def gsub (z w : Gaussian) : Gaussian := gadd z (gneg w)
def gmul (z w : Gaussian) : Gaussian :=
  ⟨z.re*w.re-z.im*w.im, z.re*w.im+z.im*w.re⟩
def gscale (c : Rat) (z : Gaussian) : Gaussian := ⟨c*z.re, c*z.im⟩
def gnorm (z : Gaussian) : Rat := qabs z.re + qabs z.im
def gpow (z : Gaussian) : Nat → Gaussian
  | 0 => gone
  | n + 1 => gmul (gpow z n) z
def ginv (z : Gaussian) : Gaussian :=
  let d := z.re*z.re+z.im*z.im
  if d = 0 then gzero else ⟨z.re/d, -z.im/d⟩

def nsum (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun a i => a + f i) 0
def qsum (n : Nat) (f : Nat → Rat) : Rat :=
  (List.range n).foldl (fun a i => a + f i) 0
def gsum (n : Nat) (f : Nat → Gaussian) : Gaussian :=
  (List.range n).foldl (fun a i => gadd a (f i)) gzero

def binomial : Nat → Nat → Nat
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j => if j = 0 then 1 else binomial n (j-1) + binomial n j

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

def entryNat (xs : List (List Nat)) (i j : Nat) : Nat :=
  (xs[i]?.getD [])[j]?.getD 0
def entryRat (xs : List (List Rat)) (i j : Nat) : Rat :=
  (xs[i]?.getD [])[j]?.getD 0
def entryG (xs : List (List Gaussian)) (i j : Nat) : Gaussian :=
  (xs[i]?.getD [])[j]?.getD gzero

structure Parameters where
  degreeX : Nat
  degreeY : Nat
  rootBound : Nat
  inverseBound : Nat
  coefficientBounds : List (List Nat)
  deriving Repr

def A (p : Parameters) : Nat := p.rootBound + 1
def J (p : Parameters) : Nat := max p.degreeY 1
def C (p : Parameters) (i l : Nat) : Nat := entryNat p.coefficientBounds i l
def M1 (p : Parameters) : Nat :=
  nsum (p.degreeY+1) (fun l => if l = 0 then 0 else l*C p 0 l*A p^(l-1))
def M2 (p : Parameters) : Nat :=
  nsum (p.degreeY+1) (fun l => if l < 2 then 0 else l*(l-1)*C p 0 l*A p^(l-2))
def coarse (p : Parameters) (i j : Nat) : Nat :=
  (p.inverseBound+1) * nsum (p.degreeY+1)
    (fun l => if j ≤ l then C p i l*binomial l j*A p^(l-j) else 0)
    + if i = 0 ∧ j = 1 then 1 else 0
def U (p : Parameters) : Nat :=
  1 + nsum (p.degreeX+1) (fun i => nsum (J p+1) (fun j => (1+j)*coarse p i j))
def T (p : Parameters) : Nat :=
  1+(p.inverseBound+1)*M1 p+M1 p+(p.inverseBound+1)*M2 p
def W (p : Parameters) : Nat :=
  1+(p.inverseBound+1)*nsum (p.degreeY+1) (fun l => (l+1)*A p^l)

structure Constants where
  h : Nat
  r : Nat
  rootPrecision : Nat
  coefficientPrecision : Nat
  deriving Repr, DecidableEq

def constants (p : Parameters) : Constants :=
  let h := bitLength (8*U p)
  ⟨h, 2*h, h+bitLength (8*T p), h+4+bitLength (W p)⟩

abbrev GName := Nat → Gaussian
abbrev CoeffNames := Nat → Nat → Nat → Gaussian

/-- A symmetric dyadic Cauchy convention; every sample has error at most 2^-s
from the represented value.  Componentwise names can be shifted by one bit. -/
def Regular (a : GName) : Prop :=
  ∀ s t, gnorm (gsub (a s) (a t)) ≤ dyadic s + dyadic t
def NameBound (a : GName) (B : Nat) : Prop :=
  ∀ s, gnorm (a s) ≤ (B : Rat) + dyadic s

def evalZeroSample (p : Parameters) (c : CoeffNames) (b : Gaussian) (s : Nat) : Gaussian :=
  gsum (p.degreeY+1) (fun l => gmul (c 0 l s) (gpow b l))
def derivativeSample (p : Parameters) (c : CoeffNames) (b : Gaussian) (s : Nat) : Gaussian :=
  gsum (p.degreeY+1) (fun l => if l = 0 then gzero else
    gscale (l : Rat) (gmul (c 0 l s) (gpow b (l-1))))

/-- Coefficient of X^i Z^j in Z-v*P(X,a+Z), using coefficient samples at s. -/
def operatorSample (p : Parameters) (c : CoeffNames)
    (a v : Gaussian) (i j s : Nat) : Gaussian :=
  gsub (if i = 0 ∧ j = 1 then gone else gzero)
    (gmul v (gsum (p.degreeY+1) (fun l => if j ≤ l then
      gscale (binomial l j : Rat) (gmul (c i l s) (gpow a (l-j))) else gzero)))

def qmin (x y : Rat) : Rat := if x ≤ y then x else y

structure Output where
  sampleCentre : Gaussian
  sampleInverse : Gaussian
  majorants : List (List Rat)
  deriving Repr

def produce (p : Parameters) (c : CoeffNames) (b w : GName) : Output :=
  let k := constants p
  let a := b k.rootPrecision
  let v := w k.rootPrecision
  let eps := dyadic k.h / 16
  let q0 := operatorSample p c a v 0 0 k.coefficientPrecision
  let q1 := operatorSample p c a v 0 1 k.coefficientPrecision
  let u00 := qmin (coarse p 0 0 : Rat) (gnorm q0 + eps)
  let u01 := qmin (coarse p 0 1 : Rat) (gnorm q1 + eps)
  let us := (List.range (p.degreeX+1)).map (fun i =>
    (List.range (J p+1)).map (fun j =>
      if i = 0 ∧ j = 0 then u00 else
      if i = 0 ∧ j = 1 then u01 else (coarse p i j : Rat)))
  ⟨a, v, us⟩

def constantBound (p : Parameters) (o : Output) : Rat :=
  qsum (p.degreeX+1) (fun i => entryRat o.majorants i 0 * dyadic (constants p).r ^ i)
def contractionBound (p : Parameters) (o : Output) : Rat :=
  qsum (p.degreeX+1) (fun i => qsum (J p+1) (fun j => if j = 0 then 0 else
    (j : Rat)*entryRat o.majorants i j*dyadic (constants p).r^i*
      dyadic (constants p).h^(j-1)))
def NumericCertificate (p : Parameters) (o : Output) : Prop :=
  o.sampleInverse ≠ gzero ∧
  constantBound p o ≤ dyadic (constants p).h/2 ∧ contractionBound p o ≤ 1/2

/-! Concrete arithmetic form of the named root/inverse hypotheses.

The residual budgets bound raw polynomial evaluation on same-stage samples.
Regularity and the displayed dyadic residuals express exact root and inverse
identities without mentioning an unspecified real or complex type.
-/

def rootBudget (p : Parameters) : Nat :=
  1+nsum (p.degreeY+1) (fun l => A p^l)+M1 p
def derivativeBudget (p : Parameters) : Nat :=
  1+nsum (p.degreeY+1) (fun l => if l = 0 then 0 else l*A p^(l-1))+M2 p
def inverseBudget (p : Parameters) : Nat :=
  1+M1 p+(p.inverseBound+1)*derivativeBudget p

structure NamedChartHypotheses (p : Parameters) (c : CoeffNames) (b w : GName) : Prop where
  coefficients_regular : ∀ i l, i ≤ p.degreeX → l ≤ p.degreeY → Regular (c i l)
  coefficients_bounded : ∀ i l, i ≤ p.degreeX → l ≤ p.degreeY → NameBound (c i l) (C p i l)
  root_regular : Regular b
  inverse_regular : Regular w
  root_bounded : NameBound b p.rootBound
  inverse_bounded : NameBound w p.inverseBound
  root_identity : ∀ s, gnorm (evalZeroSample p c (b s) s) ≤ (rootBudget p : Rat)*dyadic s
  inverse_identity : ∀ s,
    gnorm (gsub gone (gmul (w s) (derivativeSample p c (b s) s))) ≤
      (inverseBudget p : Rat)*dyadic s

/-- Error budget for one translated coefficient sampled at stage s. -/
def coefficientBudget (p : Parameters) (j : Nat) : Nat :=
  (p.inverseBound+1)*nsum (p.degreeY+1)
    (fun l => if j ≤ l then binomial l j*A p^(l-j) else 0)

def NamedMajorants (p : Parameters) (c : CoeffNames) (o : Output) : Prop :=
  ∀ i j s, i ≤ p.degreeX → j ≤ J p →
    gnorm (operatorSample p c o.sampleCentre o.sampleInverse i j s) ≤
      entryRat o.majorants i j + (coefficientBudget p j : Rat)*dyadic s

/-- UNPROVED: the fixed precision formulas are sufficient. -/
def PrecisionBoundsTarget : Prop :=
  ∀ p : Parameters,
    (U p : Rat)*dyadic (constants p).h ≤ 1/8 ∧
    (U p : Rat)*dyadic (constants p).r ≤ dyadic (constants p).h/8 ∧
    dyadic (constants p).rootPrecision ≤ dyadic (constants p).h/(8*(T p : Rat)) ∧
    (W p : Rat)*dyadic (constants p).coefficientPrecision ≤ dyadic (constants p).h/16

/-- UNPROVED: the main producer target, with every hypothesis and output
predicate expressed through rational arithmetic on explicitly named samples. -/
def NamedProducerTarget : Prop :=
  ∀ (p : Parameters) (c : CoeffNames) (b w : GName),
    NamedChartHypotheses p c b w →
    let o := produce p c b w
    NumericCertificate p o ∧ NamedMajorants p c o

/-! Gaussian truncated-series kernel.  These are the concrete complex
counterparts of the real-rational arrays in `SeriesTargets`. -/

abbrev GPoly := List Gaussian
def gc (p : GPoly) (k : Nat) : Gaussian := p[k]?.getD gzero
def pzero (K : Nat) : GPoly := List.replicate (K+1) gzero
def pone (K : Nat) : GPoly := gone :: List.replicate K gzero
def padd (K : Nat) (p q : GPoly) : GPoly :=
  (List.range (K+1)).map (fun k => gadd (gc p k) (gc q k))
def psub (K : Nat) (p q : GPoly) : GPoly :=
  (List.range (K+1)).map (fun k => gsub (gc p k) (gc q k))
def pmul (K : Nat) (p q : GPoly) : GPoly :=
  (List.range (K+1)).map (fun k => gsum (k+1) (fun i => gmul (gc p i) (gc q (k-i))))
def ppow (K : Nat) (p : GPoly) : Nat → GPoly
  | 0 => pone K
  | n+1 => pmul K (ppow K p n) p
def pshift (K i : Nat) (c : Gaussian) (p : GPoly) : GPoly :=
  (List.range (K+1)).map (fun k => if i ≤ k then gmul c (gc p (k-i)) else gzero)
def pnorm (K : Nat) (R : Rat) (p : GPoly) : Rat :=
  qsum (K+1) (fun k => gnorm (gc p k)*R^k)
def operatorApply (K e d : Nat) (F : List (List Gaussian)) (p : GPoly) : GPoly :=
  (List.range (e+1)).foldl (fun acc i =>
    (List.range (d+1)).foldl (fun row j =>
      padd K row (pshift K i (entryG F i j) (ppow K p j))) acc) (pzero K)

def FiniteSeriesCertificate (e d : Nat) (F : List (List Gaussian))
    (u : List (List Rat)) (R rho : Rat) : Prop :=
  0 < R ∧ R ≤ 1 ∧ 0 < rho ∧ rho ≤ 1 ∧
  (∀ i j, i ≤ e → j ≤ d → gnorm (entryG F i j) ≤ entryRat u i j) ∧
  qsum (e+1) (fun i => entryRat u i 0*R^i) ≤ rho/2 ∧
  qsum (e+1) (fun i => qsum (d+1) (fun j => if j = 0 then 0 else
    (j : Rat)*entryRat u i j*R^i*rho^(j-1))) ≤ 1/2

/-- UNPROVED: convolution inequality over Gaussian rational arrays. -/
def GaussianNormProductTarget : Prop :=
  ∀ K R (p q : GPoly), 0 ≤ R → pnorm K R (pmul K p q) ≤ pnorm K R p*pnorm K R q

/-- UNPROVED: the finite complex contraction kernel needed by the producer. -/
def GaussianContractionTarget : Prop :=
  ∀ K e d F u R rho (p q : GPoly), FiniteSeriesCertificate e d F u R rho →
    pnorm K R p ≤ rho → pnorm K R q ≤ rho →
    pnorm K R (operatorApply K e d F p) ≤ rho ∧
    pnorm K R (psub K (operatorApply K e d F p) (operatorApply K e d F q)) ≤
      (1/2)*pnorm K R (psub K p q)

/-!
Proof completion order:
1. Prove |z*w|₁≤|z|₁|w|₁ and the finite Gaussian convolution bounds.
2. Prove the finite polynomial first and second derivative difference bounds
   M1,M2, by the difference-of-powers identity.
3. Prove `PrecisionBoundsTarget` from the binary-length inequality.
4. From named root/inverse identities derive the two small coefficient
   estimates at the fixed rootPrecision; the arbitrary observation precision
   is introduced before any bounded rational induction.
5. Prove the linear-in-input coefficient sampling budgets and correctness of
   taking the minimum of two upper bounds; conclude `NamedProducerTarget`.
6. Lift the Gaussian contraction proof to the coefficient/tail construction
   of the article.  Reify the fixed rational algorithms and construct the
   `Prf PRAAx` derivations separately.  No host target supplies those objects.
-/

def sampleParameters : Parameters := ⟨0, 1, 1, 1, [[1, 1]]⟩

-- Only these closed formula checks are asserted; the named targets remain unproved.
example : constants sampleParameters = ⟨7, 14, 13, 15⟩ := by decide +kernel
example : gmul ⟨1, 1⟩ ⟨1, -1⟩ = ⟨2, 0⟩ := by decide +kernel
example : gnorm ⟨-(1/3), 2/3⟩ = 1 := by decide +kernel

end IPRAFramework.ChartProducer
