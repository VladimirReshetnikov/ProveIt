import ConciseIPRA.PR
import Mathlib.Data.Rat.Defs

/-!
# Constructive FTA in iPRA: UNCOMPILED specification and proof interfaces

This is an outline, not a completed formalization. No certificate type below
is inhabited here, and no FTA theorem is postulated.

The repository API was inspected at ProveIt commit
b03925cccc76d55b9dc2a00864a5e0544b64aa7f (Lean/mathlib v4.32.0).

The main target is positive nonconstancy: a finite upper degree n and a
supplied witness |a_k(h+2)| >= 2^(-h), with 1 <= k <= n. Higher coefficients
may have undecidable equality to zero. No monicity or leading-coefficient
test is required.

The arithmetic formula builders below are explicit. Their remaining PR-code
parameters are implementation interfaces whose arithmetic meanings MUST be
proved. Choosing arbitrary codes does not establish FTA. In particular the
metalevel certificate type is only the final task to be completed.

There is no assumed primitive-recursive universal evaluator. A coefficient
program is a fixed PR syntax tree, and compilation constructs further trees.
-/

namespace IPRAFTA

open LeanProofs.ConciseIPRA

/-! ## Readable finite rational specifications -/

structure GQ where
  re : ℚ
  im : ℚ

namespace GQ

def zero : GQ := ⟨0, 0⟩
def one : GQ := ⟨1, 0⟩
def add (z w : GQ) : GQ := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : GQ) : GQ := ⟨-z.re, -z.im⟩
def sub (z w : GQ) : GQ := add z (neg w)
def mul (z w : GQ) : GQ :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def normSq (z : GQ) : ℚ := z.re * z.re + z.im * z.im

def pow (z : GQ) : ℕ → GQ
  | 0 => one
  | k + 1 => mul (pow z k) z

def sumBelow (f : ℕ → GQ) : ℕ → GQ
  | 0 => zero
  | k + 1 => add (sumBelow f k) (f k)

/-- All n+1 coefficients are supplied; n is only an upper degree. -/
def eval (n : ℕ) (a : ℕ → GQ) (z : GQ) : GQ :=
  sumBelow (fun i => mul (a i) (pow z i)) (n + 1)

def within (z w : GQ) (e : ℚ) : Prop :=
  0 ≤ e ∧ normSq (sub z w) ≤ e * e

end GQ

def dyadic (t : ℕ) : ℚ := 1 / (2 : ℚ) ^ t
def descentD (n : ℕ) : ℕ := 2 ^ n * 4 ^ (2 * n * n)
def descentQ (n : ℕ) : ℚ := 1 - 1 / (4 * (descentD n : ℚ))
def outerQ (n : ℕ) : ℚ := 1 - 1 / (8 * (descentD n : ℚ))
def blockLength (n : ℕ) : ℕ := 8 * n * descentD n
def outerRho (n : ℕ) : ℚ := 1 - 1 / (blockLength n : ℚ)
def stepConstant (B n h : ℕ) : ℕ := B * n * 2 ^ (n + h + 1)
def radiusBound (C K A₀ : ℕ) : ℕ := 2 * (1 + C) ^ (K * A₀)
def sampleIndex (K H t : ℕ) : ℕ := K * (t + H + 2)

/-- This unbounded input assumption is retained in the context; it is
not used as the matrix of an induction instance. -/
def CoeffCauchy (n : ℕ) (a : ℕ → ℕ → GQ) : Prop :=
  ∀ i, i ≤ n → ∀ s t,
    GQ.within (a i s) (a i t) (dyadic s + dyadic t)

def ApartWitness (n k h : ℕ) (a : ℕ → ℕ → GQ) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ dyadic (2 * h) ≤ GQ.normSq (a k (h + 2))

/-- The exact finite outputs, including stability under later coefficient
sampling. No completed field or existence of a limit occurs in this type. -/
structure RootNameBounds
    (n L K H R : ℕ) (a : ℕ → ℕ → GQ) (alpha : ℕ → GQ) : Prop where
  cauchy : ∀ t u, t ≤ u →
    GQ.within (alpha u) (alpha t) (dyadic (t + 2))
  sampledResidual : ∀ t,
    GQ.within
      (GQ.eval n (fun i => a i (sampleIndex K H t + L)) (alpha t))
      GQ.zero (dyadic (t + 2))
  laterResidual : ∀ t s, sampleIndex K H t + L ≤ s →
    GQ.within (GQ.eval n (fun i => a i s) (alpha t))
      GQ.zero (dyadic t)
  radius : ∀ t, GQ.normSq (alpha t) ≤ (R : ℚ) ^ 2

/-- b is the rational Taylor coefficient tuple of P at z.
The actual translation identity is a separate required lemma. -/
def DescentBounds
    (n : ℕ) (a b : ℕ → GQ) (z w : GQ) (r₀ : ℚ) : Prop :=
  0 ≤ r₀ ∧
  GQ.normSq (GQ.eval n a (GQ.add z w)) ≤
    descentQ n ^ 2 * GQ.normSq (GQ.eval n a z) ∧
  GQ.normSq w ≤ r₀ ^ 2 ∧
  ∀ i, 1 ≤ i → i ≤ n →
    GQ.normSq (b i) * r₀ ^ (2 * i) ≤ GQ.normSq (b 0)

/-- Optional finite audit record; entries must be checked, not trusted. -/
structure DescentRecord where
  polynomial : ℕ
  point : ℕ
  translatedCoefficients : ℕ
  heightBound : ℕ
  firstRadiusIndex : ℕ
  maximizingIndices : ℕ
  plateauCenter : ℕ
  dominantExponent : ℕ
  direction : ℕ
  radius : ℕ
  step : ℕ
  nextPoint : ℕ

structure IterationRecord where
  degreeUpper : ℕ
  witnessIndex : ℕ
  witnessHeight : ℕ
  boundB : ℕ
  offsetL : ℕ
  horizon : ℕ
  coefficientTable : ℕ
  points : ℕ
  steps : ℕ
  auxiliaryProducts : ℕ
  descentRecords : ℕ

/-! ## Primitive-recursive syntax interfaces -/

/-- Every field denotes an explicit natural-number operation after coding.
All tests return 1 for true and 0 for false.

naturalLe(x,y)          : x <= y.
nearDyadic(z,w,t)       : N(z-w) <= 2^(-2t).
nearDyadicSum(z,w,s,t)  : N(z-w) <= (2^(-s)+2^(-t))^2.
normGeDyadic(z,h)       : N(z) >= 2^(-2h).
normLeDyadic(z,t)       : N(z) <= 2^(-2t).
normLeInteger(z,R)      : N(z) <= R^2.

The implementation must prove representation and Boolean correctness.
-/
structure ArithmeticCodes where
  add : PR 2
  naturalLe : PR 2
  nearDyadic : PR 3
  nearDyadicSum : PR 4
  normGeDyadic : PR 2
  normLeDyadic : PR 2
  normLeInteger : PR 2

/-- A fixed PR coefficient program and numerical input selectors.
The r parameters can include n,k,h, so the algorithm and theorem may
be uniform in those natural-number parameters.
-/
structure FixedCoefficientProgram (r : ℕ) where
  coefficient : PR (r + 2) -- i, precision, then r numerical parameters
  upperDegree : PR r
  witnessIndex : PR r
  witnessHeight : PR r

/-- The output PR syntax to be constructed, never an assumed oracle.
evalAt(s,t,parameters) evaluates the polynomial using coefficient precision s
and root approximation alpha(t). Its coefficient routine is compiled from
the FIXED input program, not implemented by a universal PR evaluator.
-/
structure CompiledNameProgram (r : ℕ) where
  root : PR (r + 1)       -- t, parameters
  evalAt : PR (r + 2)     -- s, t, parameters
  sampleJ : PR (r + 1)    -- t, parameters
  boundB : PR r
  offsetL : PR r
  exponentH : PR r
  radiusR : PR r
  iteration : PR (r + 1)  -- j, parameters

/-! ## Explicit object-language formula builders -/

def numeral {s : ℕ} : ℕ → PTm s
  | 0 => PTm.zero
  | n + 1 => PTm.succ (numeral n)

def app2 {s : ℕ} (f : PR 2) (x y : PTm s) : PTm s :=
  PTm.app f (Fin.cases x (Fin.cases y Fin.elim0))

def app3 {s : ℕ} (f : PR 3) (x y z : PTm s) : PTm s :=
  PTm.app f (Fin.cases x (Fin.cases y (Fin.cases z Fin.elim0)))

def app4 {s : ℕ} (f : PR 4) (w x y z : PTm s) : PTm s :=
  PTm.app f
    (Fin.cases w (Fin.cases x (Fin.cases y (Fin.cases z Fin.elim0))))

def isOne {s : ℕ} (t : PTm s) : Fm PTm s :=
  Fm.eq t (numeral 1)

/-- Lift the parameter environment under b new object-language binders. -/
def liftEnv {r s : ℕ} (e : Fin r → PTm s) :
    (b : ℕ) → Fin r → PTm (s + b)
  | 0 => e
  | b + 1 => fun i => Syn.shift (liftEnv e b i)

def coeffAt {r s : ℕ} (A : FixedCoefficientProgram r)
    (i t : PTm s) (e : Fin r → PTm s) : PTm s :=
  PTm.app A.coefficient (Fin.cases i (Fin.cases t e))

def rootAt {r s : ℕ} (Z : CompiledNameProgram r)
    (t : PTm s) (e : Fin r → PTm s) : PTm s :=
  PTm.app Z.root (Fin.cases t e)

def polyAt {r s : ℕ} (Z : CompiledNameProgram r)
    (samp t : PTm s) (e : Fin r → PTm s) : PTm s :=
  PTm.app Z.evalAt (Fin.cases samp (Fin.cases t e))

def precisionAt {r s : ℕ} (o : ArithmeticCodes) (Z : CompiledNameProgram r)
    (t : PTm s) (e : Fin r → PTm s) : PTm s :=
  app2 o.add (PTm.app Z.sampleJ (Fin.cases t e)) (PTm.app Z.offsetL e)

def closeAll : (n : ℕ) → Fm PTm n → Fm PTm 0
  | 0, phi => phi
  | n + 1, phi => closeAll n (Fm.all phi)

/-- Inner variables: 0=t, 1=s, 2=i, followed by the input parameters. -/
def coefficientCauchyMatrix {r : ℕ}
    (o : ArithmeticCodes) (A : FixedCoefficientProgram r) : Fm PTm (r + 3) :=
  let e := liftEnv (fun j : Fin r => PTm.var j) 3
  let i : PTm (r + 3) := PTm.var 2
  let s : PTm (r + 3) := PTm.var 1
  let t : PTm (r + 3) := PTm.var 0
  Fm.imp
    (isOne (app2 o.naturalLe i (PTm.app A.upperDegree e)))
    (isOne (app4 o.nearDyadicSum (coeffAt A i s e) (coeffAt A i t e) s t))

def inputHypothesis {r : ℕ}
    (o : ArithmeticCodes) (A : FixedCoefficientProgram r) : Fm PTm r :=
  let e := fun j : Fin r => PTm.var j
  let n := PTm.app A.upperDegree e
  let k := PTm.app A.witnessIndex e
  let h := PTm.app A.witnessHeight e
  Fm.and
    (isOne (app2 o.naturalLe (numeral 1) k))
    (Fm.and
      (isOne (app2 o.naturalLe k n))
      (Fm.and
        (isOne (app2 o.normGeDyadic (coeffAt A k (app2 o.add h (numeral 2)) e) h))
        (Fm.all (Fm.all (Fm.all (coefficientCauchyMatrix o A))))))

/-- Inner variables: 0=u, 1=t. This is syntactically quantifier-free. -/
def cauchyMatrix {r : ℕ}
    (o : ArithmeticCodes) (Z : CompiledNameProgram r) : Fm PTm (r + 2) :=
  let e := liftEnv (fun j : Fin r => PTm.var j) 2
  let u : PTm (r + 2) := PTm.var 0
  let t : PTm (r + 2) := PTm.var 1
  Fm.imp
    (isOne (app2 o.naturalLe t u))
    (isOne (app3 o.nearDyadic (rootAt Z u e) (rootAt Z t e)
      (app2 o.add t (numeral 2))))

def sampledResidualMatrix {r : ℕ}
    (o : ArithmeticCodes) (Z : CompiledNameProgram r) : Fm PTm (r + 1) :=
  let e := liftEnv (fun j : Fin r => PTm.var j) 1
  let t : PTm (r + 1) := PTm.var 0
  isOne (app2 o.normLeDyadic (polyAt Z (precisionAt o Z t e) t e)
    (app2 o.add t (numeral 2)))

/-- Inner variables: 0=s, 1=t. Covers every later coefficient sample. -/
def laterResidualMatrix {r : ℕ}
    (o : ArithmeticCodes) (Z : CompiledNameProgram r) : Fm PTm (r + 2) :=
  let e := liftEnv (fun j : Fin r => PTm.var j) 2
  let s : PTm (r + 2) := PTm.var 0
  let t : PTm (r + 2) := PTm.var 1
  Fm.imp
    (isOne (app2 o.naturalLe (precisionAt o Z t e) s))
    (isOne (app2 o.normLeDyadic (polyAt Z s t e) t))

def radiusMatrix {r : ℕ}
    (o : ArithmeticCodes) (Z : CompiledNameProgram r) : Fm PTm (r + 1) :=
  let e := liftEnv (fun j : Fin r => PTm.var j) 1
  let t : PTm (r + 1) := PTm.var 0
  isOne (app2 o.normLeInteger (rootAt Z t e) (PTm.app Z.radiusR e))

def conclusion {r : ℕ}
    (o : ArithmeticCodes) (Z : CompiledNameProgram r) : Fm PTm r :=
  Fm.and (Fm.all (Fm.all (cauchyMatrix o Z)))
    (Fm.and (Fm.all (sampledResidualMatrix o Z))
      (Fm.and (Fm.all (Fm.all (laterResidualMatrix o Z)))
        (Fm.all (radiusMatrix o Z))))

def ftaSentence {r : ℕ} (o : ArithmeticCodes)
    (A : FixedCoefficientProgram r) (Z : CompiledNameProgram r) : Fm PTm 0 :=
  closeAll r (Fm.imp (inputHypothesis o A) (conclusion o Z))

/-- THE required endpoint, as a type only. No inhabitant is supplied. -/
structure NativeDerivationCertificate {r : ℕ}
    (o : ArithmeticCodes) (A : FixedCoefficientProgram r)
    (Z : CompiledNameProgram r) : Prop where
  derivation : Prf PRAAx [] (ftaSentence o A Z)

/-! ## Finite-table and rational-input specialization targets -/

/-- Inputs: n,k,h,B,L,horizon,coefficient table,trajectory.
The invariant Boolean fold includes the product U_j and its bound R.
All meanings require explicit representation proofs.
-/
structure FiniteTableCodes where
  tableAdmissible : PR 8
  trajectoryComputed : PR 8
  invariantHolds : PR 8

def finiteTableSentence (c : FiniteTableCodes) : Fm PTm 0 :=
  closeAll 8
    (Fm.imp
      (Fm.and
        (isOne (PTm.app c.tableAdmissible PTm.var))
        (isOne (PTm.app c.trajectoryComputed PTm.var)))
      (isOne (PTm.app c.invariantHolds PTm.var)))

structure FiniteTableDerivation (c : FiniteTableCodes) : Prop where
  derivation : Prf PRAAx [] (finiteTableSentence c)

/-- Single-input rational polynomial encoding.
The validity predicate checks the code and the finite nonconstant witness.
Coefficients are constant names; their precision argument is ignored.
-/
structure RationalInputCodes where
  coefficient : PR 2 -- i, polynomial code
  upperDegree : PR 1
  witnessIndex : PR 1
  witnessHeight : PR 1
  valid : PR 1

def constantNameInput (c : RationalInputCodes) : FixedCoefficientProgram 1 where
  coefficient := PR.comp c.coefficient
    (Fin.cases (PR.proj (0 : Fin 3))
      (Fin.cases (PR.proj (2 : Fin 3)) Fin.elim0))
  upperDegree := c.upperDegree
  witnessIndex := c.witnessIndex
  witnessHeight := c.witnessHeight

def rationalSentence (o : ArithmeticCodes) (c : RationalInputCodes)
    (Z : CompiledNameProgram 1) : Fm PTm 0 :=
  closeAll 1
    (Fm.imp (isOne (PTm.app c.valid PTm.var)) (conclusion o Z))

structure RationalDerivationCertificate (o : ArithmeticCodes)
    (c : RationalInputCodes) (Z : CompiledNameProgram 1) : Prop where
  derivation : Prf PRAAx [] (rationalSentence o c Z)

/-!
Implementation obligations deliberately not declared as axioms:

1. Construct ArithmeticCodes and prove their representations.
2. Construct the primitive-recursive rational descent and direction codes.
3. Prove finiteTableSentence using the actual PRA.qfInd rule.
4. For each fixed A, construct Z by PR composition and primitive recursion;
   prove its equations and its correspondence with B,C,D,K,A0,R,L,H,J.
5. Construct NativeDerivationCertificate for those verified codes.
6. Prove valid -> inputHypothesis for constantNameInput, then obtain the
   RationalDerivationCertificate by intuitionistic implication elimination.

PRA.qfInd is already provided by ConciseIPRA.PR. Its matrix must be QF.
Compile bounded sums, products, maxima, and universal finite checks to PR
functions and Boolean equations before applying it.

After the object derivation exists, pra_iff_native from
ConciseIPRA.NativeBiInterpretation supplies the optional native-calculus
translation. A theorem about standard ℂ or a semantic soundness argument
cannot replace construction of the object derivation.
-/

end IPRAFTA

