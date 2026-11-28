import IPRADerivations.AnalyticNumberTheory.Riemann.Lagarias
import IPRADerivations.AnalyticNumberTheory.Riemann.UniversalCriteria
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`RobinNicolas.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Exact rational certificates for the Robin, Nicolas and scaled totient criteria.
The analytic equivalences and endpoint convergence proofs are in the report. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.RobinNicolas
open LeanProofs.ConciseIPRA PacketLanguage Discrete
open scoped Fm
open SplitPrimes (readEq readIte readLe readLog)
open SplitPrimes renaming read1 → readUnary

/-- Pair of numerator and denominator expressions in one finite scope. -/
private abbrev Fraction (ctx : List String) := E ctx × E ctx
private def add {ctx} (x y : Fraction ctx) : Fraction ctx :=
  (x.1*y.2+y.1*x.2, x.2*y.2)
private def mul {ctx} (x y : Fraction ctx) : Fraction ctx :=
  (x.1*y.1, x.2*y.2)
private def positiveDifference {ctx} (x y : Fraction ctx) : Fraction ctx :=
  (x.1*y.2-y.1*x.2, x.2*y.2)
private def positiveNumerator {ctx} (x y : Fraction ctx) : E ctx :=
  x.1*y.2-y.1*x.2

/-- For a/b ≥ 1, integrate 1/x from 1 to a/b on m equal panels,
using left endpoints for the upper estimate and right endpoints for the lower. -/
private def logNumerator (upper : Bool) : PR 3 := program ["a","b","m"] <|
  (v "a"-v "b") * (sumTo "j" (v "m") <|
    let diff := v "a"-v "b"
    let den := v "b"*v "m"
    let index := if upper then v "j" else v "j"+1
    divE (call Lagarias.commonDen [diff,den,v "m"]) (den+index*diff))

private def logRatio {ctx} (upper : Bool) (x : Fraction ctx) (m : E ctx) : Fraction ctx :=
  let a := call maxR [x.1,x.2]
  (call (logNumerator upper) [a,x.2,m], call Lagarias.commonDen [a-x.2,x.2*m,m])

/-- Use a binary exponent so the first logarithm integrates only on [1,2]. -/
private def logInteger {ctx} (upper : Bool) (n m : E ctx) : Fraction ctx :=
  let h := call logCode [n]
  add (mul (h,1) (logRatio upper (2,1) m)) (logRatio upper (n,powE 2 h) m)

/-- Upper and lower binomial enclosures of exp(gamma); m ≥ 1, r=2m. -/
private def expGamma {ctx} (upper : Bool) (m : E ctx) : Fraction ctx :=
  let den := call Lagarias.factorial [m]
  let num := call Lagarias.harmonicNumerator [m]
  let r := 2*m
  let w := r*den
  if upper then (powE w r, m*powE (w-num) r)
  else (powE (w+num) r,(m+1)*powE w r)

private def threshold {ctx} (upper : Bool) (n m : E ctx) : Fraction ctx :=
  mul (expGamma upper m) (logRatio upper (logInteger upper n m) m)

/-- All distinct primorials of interest appear using cutoffs y ≥ 3. -/
def primeProduct (totient : Bool) : PR 1 := program ["y"] <|
  prodTo "p" (v "y"+1) (iteE (eqB (call primeCode [v "p"]) 1)
    (if totient then v "p"-1 else v "p") 1)

inductive Named where | robin | nicolas deriving DecidableEq

private abbrev ctx := ["s","j"]
private def namedParts (c : Named) (upper : Bool) : Fraction ctx × Fraction ctx :=
  let m := v "j"+1
  match c with
  | .robin =>
    let n := v "s"+5041
    ((call Lagarias.divisorSum [n],n),threshold upper n m)
  | .nicolas =>
    let y := v "s"+3
    let P := call (primeProduct false) [y]
    (threshold upper P m,(P,call (primeProduct true) [y]))

/-- Positive margin is a strict certificate. Positive excess refutes the weak
comparison at that precision. The two use opposite enclosing endpoints. -/
def margin (c : Named) (strict : Bool) : PR 2 := program ctx <|
  let upper := match c with | .robin => !strict | .nicolas => strict
  let (lhs,rhs) := namedParts c upper
  if strict then positiveNumerator rhs lhs else positiveNumerator lhs rhs

/-- The four-field adapter allows the existing first-success extractor to run
with the input n or y fixed, scanning only the approximation precision. -/
private def withParameters (f : PR 2) : PR 5 :=
  .comp f (Fin.cases (.proj 0) (fun _ => .proj 4))

private def outer : Fin 4 → PTm 1 := Fin.cases (Syn.var 0) (fun _ => PTm.zero)

def strictForm (c : Named) : Fm PTm 0 :=
  .all (PacketAudit.anyFailure (withParameters (margin c true)) outer)

def firstCertificate (c : Named) : Fm PTm 0 :=
  .all (PacketAudit.earliestFailure (withParameters (margin c true)) outer)

theorem strict_iff_first (c : Named) :
    Prf PRAAx [] (Fm.iff (strictForm c) (firstCertificate c)) := by
  have h := PacketAudit.failure_iff_first (withParameters (margin c true)) outer
  apply Prf.iffI <;> apply Prf.impI <;> apply Prf.allI
  · exact Prf.iffMp (Prf.ofNil h) (Prf.allOpen Prf.hyp0)
  · exact Prf.iffMpr (Prf.ofNil h) (Prf.allOpen Prf.hyp0)

private def pair {α : Type} (a b : α) : Fin 2 → α := Fin.cases a (fun _ => b)
def universal (f : PR 2) : Fm PTm 0 :=
  .all (.all (.eq (.app f (pair (Syn.var 1) (Syn.var 0))) PTm.zero))

def weak (c : Named) := universal (margin c false)

inductive Direction where | above | below | both

/-- A one-sided weak bound of 5 for the scaled primorial error, or a simultaneous
bound of 5 on the absolute value. Use the inner endpoint for each sign. -/
def scaledMatrix (side : Direction) : PR 2 := program ctx <|
  let m := v "j"+1
  let y := v "s"+3
  let P := call (primeProduct false) [y]
  let ratio := (P,call (primeProduct true) [y])
  let test := fun (a : Fraction ctx) =>
    positiveNumerator (mul (mul a a) (logInteger false P m)) (25,1)
  let up := test (positiveDifference ratio (threshold true P m))
  let lo := test (positiveDifference (threshold false P m) ratio)
  match side with | .above => up | .below => lo | .both => up+lo

def scaled (d : Direction) := universal (scaledMatrix d)

theorem universal_reading (f : PR 2) : naturalTerms.Holds (universal f) Fin.elim0 ↔
    ∀ s j, value f (pair s j) = 0 := by
  change (∀ s j, value f _ = 0) ↔ _
  apply forall_congr'; intro s
  apply forall_congr'; intro j
  have h : (fun i => termValue (pair (Syn.var 1) (Syn.var 0) i)
        (Fin.cases j (Fin.cases s Fin.elim0))) = pair s j :=
    funext (Fin.cases rfl (fun _ => rfl))
  rw [h]

theorem strict_reading (c : Named) : naturalTerms.Holds (strictForm c) Fin.elim0 ↔
    ∀ s, ∃ j, value (margin c true) (pair s j) ≠ 0 := by
  change (∀ s, ∃ j, (value (withParameters (margin c true)) _ = 0 → False)) ↔ _
  apply forall_congr'; intro s
  apply exists_congr; intro j
  rw [withParameters, value]
  apply iff_of_eq
  apply congrArg (fun z : Nat => z ≠ 0)
  apply congrArg (value (margin c true))
  funext i
  exact Fin.cases rfl (fun _ => rfl) i


/-! Native integer pairs are unreduced rationals. Leaving their denominators
unreduced agrees with the actual cross-products in each PR margin. -/
abbrev QPair := Nat × Nat
def plusQ (x y : QPair) : QPair := (x.1*y.2+y.1*x.2,x.2*y.2)
def timesQ (x y : QPair) : QPair := (x.1*y.1,x.2*y.2)
def excessQ (x y : QPair) := x.1*y.2-y.1*x.2
def diffQ (x y : QPair) : QPair := (excessQ x y,x.2*y.2)
def ltQ (x y : QPair) := x.1*y.2 < y.1*x.2
def leQ (x y : QPair) := x.1*y.2 ≤ y.1*x.2

def commonNat (a b m : Nat) :=
  overRange 1 (fun j p => p*(b+j*a)) (m+1)

def logPair (upper : Bool) (x : QPair) (m : Nat) : QPair :=
  let a := max x.1 x.2 - x.2
  let b := x.2*m
  let D := commonNat a b m
  (a * overRange 0 (fun j s => s+D/(b+(if upper then j else j+1)*a)) m, D)

def logNat (upper : Bool) (n m : Nat) : QPair :=
  let h := n.log2
  plusQ (timesQ (h,1) (logPair upper (2,1) m)) (logPair upper (n,2^h) m)

def harmonicNum (m : Nat) := overRange 0 (fun j s => s+m.factorial/(j+1)) m

def gammaPair (upper : Bool) (m : Nat) : QPair :=
  let A := harmonicNum m
  let r := 2*m
  let w := r*m.factorial
  if upper then (w^r,m*(w-A)^r) else ((w+A)^r,(m+1)*w^r)

def boundPair (upper : Bool) (n m : Nat) : QPair :=
  timesQ (gammaPair upper m) (logPair upper (logNat upper n m) m)

def sigmaNat (n : Nat) := overRange 0 (fun j s => s+(j+1)*(if n%(j+1)=0 then 1 else 0)) n

def primorialNat (totient : Bool) (y : Nat) :=
  overRange 1 (fun p acc => acc*(if SplitPrimes.primeBit p = 1 then
    (if totient then p-1 else p) else 1)) (y+1)

def nativeParts (c : Named) (upper : Bool) (s m : Nat) : QPair × QPair :=
  match c with
  | .robin => ((sigmaNat (s+5041),s+5041),boundPair upper (s+5041) m)
  | .nicolas =>
    let P := primorialNat false (s+3)
    (boundPair upper P m,(P,primorialNat true (s+3)))

private def readF {c} (x : Fraction c) (e : Fin c.length → Nat) : QPair := (denote x.1 e,denote x.2 e)
private theorem readMk {c} (a b : E c) (e) :
    readF (a,b) e=(denote a e,denote b e) := rfl
private theorem readPlus {c} (x y : Fraction c) (e) :
    readF (add x y) e=plusQ (readF x e) (readF y e) := by
  simp only [readF,add,plusQ,Discrete.plus,Discrete.times]
private theorem readTimes {c} (x y : Fraction c) (e) :
    readF (mul x y) e=timesQ (readF x e) (readF y e) := by
  simp only [readF,mul,timesQ,Discrete.times]
private theorem readExcess {c} (x y : Fraction c) (e) :
    denote (positiveNumerator x y) e = excessQ (readF x e) (readF y e) := by
  simp only [readF,positiveNumerator,excessQ,Discrete.minus,Discrete.times]
private theorem readDiff {c} (x y : Fraction c) (e) :
    readF (positiveDifference x y) e=diffQ (readF x e) (readF y e) := by
  simp only [readF,positiveDifference,diffQ,excessQ,Discrete.minus,Discrete.times]

private theorem readSum {c} (j : String) (n : E c) (s : E (j::c)) (e) :
    denote (sumTo j n s) e = overRange 0 (fun i a => a+denote s (Fin.cases i e)) (denote n e) := rfl
private theorem readProd {c} (j : String) (n : E c) (s : E (j::c)) (e) :
    denote (prodTo j n s) e = overRange 1 (fun i a => a*denote s (Fin.cases i e)) (denote n e) := rfl
private theorem readMax {c} (a b : E c) (e) :
    denote (call maxR [a,b]) e = max (denote a e) (denote b e) := value_maxR _

private theorem readFact {c} (x : E c) (e) :
    denote (call Lagarias.factorial [x]) e = (denote x e).factorial := by
  change value Lagarias.factorial _ = _
  unfold Lagarias.factorial
  rw [value_program]
  simp only [readProd,Discrete.plus]
  change overRange 1 (fun j a => a*(j+1)) (denote x e) = _
  generalize denote x e = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.mul_comm (n+1)]
    exact congrArg (fun a => a*(n+1)) ih

private theorem readHarm {c} (x : E c) (e) :
    denote (call Lagarias.harmonicNumerator [x]) e = harmonicNum (denote x e) := by
  change value Lagarias.harmonicNumerator _ = _
  unfold Lagarias.harmonicNumerator
  rw [value_program]
  simp only [readSum,denote_divE,readFact,Discrete.plus]
  rfl

private theorem readD {c} (a b m : E c) (e) :
    denote (call Lagarias.commonDen [a,b,m]) e = commonNat (denote a e) (denote b e) (denote m e) := by
  change value Lagarias.commonDen _ = _
  unfold Lagarias.commonDen
  rw [value_program]
  simp only [readProd,Discrete.plus,Discrete.times]
  rfl

private theorem readNum {c} (upper : Bool) (x y z : E c) (e) :
    denote (call (logNumerator upper) [x,y,z]) e =
      let a := denote x e-denote y e
      let b := denote y e*denote z e
      a*overRange 0 (fun j s => s+commonNat a b (denote z e)/(b+(if upper then j else j+1)*a)) (denote z e) := by
  change value (logNumerator upper) _ = _
  cases upper <;> unfold logNumerator <;> rw [value_program] <;>
    simp only [Bool.false_eq_true,if_false,if_true,Discrete.times,Discrete.minus,readSum,denote_divE,readD,Discrete.plus] <;> rfl

private theorem readRatio {c} (upper : Bool) (x : Fraction c) (m : E c) (e) :
    readF (logRatio upper x m) e = logPair upper (readF x e) (denote m e) := by
  simp only [logRatio,readMk,readD,readNum,readMax,Discrete.minus,Discrete.times]
  rfl
private theorem readIntLog {c} (upper : Bool) (n m : E c) (e) :
    readF (logInteger upper n m) e = logNat upper (denote n e) (denote m e) := by
  simp only [logInteger,readPlus,readTimes,readRatio,readMk,readLog,Discrete.power]
  rfl
private theorem readGamma {c} (upper : Bool) (m : E c) (e) :
    readF (expGamma upper m) e = gammaPair upper (denote m e) := by
  cases upper <;> simp only [Bool.false_eq_true,if_false,if_true,expGamma,readMk,Discrete.power,Discrete.times,Discrete.plus,
    Discrete.minus,readFact,readHarm] <;> rfl
private theorem readBound {c} (upper : Bool) (n m : E c) (e) :
    readF (threshold upper n m) e = boundPair upper (denote n e) (denote m e) := by
  simp only [threshold,readTimes,readGamma,readRatio,readIntLog,boundPair]
private theorem readSigma {c} (n : E c) (e) :
    denote (call Lagarias.divisorSum [n]) e = sigmaNat (denote n e) := by
  change value Lagarias.divisorSum _ = _
  unfold Lagarias.divisorSum
  rw [value_program]
  simp only [readSum,Discrete.times,Discrete.plus,readEq,denote_modE]
  rfl
private theorem readPrimeProd {c} (b : Bool) (y : E c) (e) :
    denote (call (primeProduct b) [y]) e = primorialNat b (denote y e) := by
  change value (primeProduct b) _ = _
  unfold primeProduct
  rw [value_program]
  unfold primorialNat
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true,readProd,Discrete.plus,readIte,readEq,readUnary,Discrete.minus] <;>
    apply congrArg (fun f => overRange 1 f (denote y e+1)) <;> funext p a <;>
      change a*(if (if SplitPrimes.primeBit p=1 then 1 else 0)=0 then 1 else _) = _ <;>
      by_cases h : SplitPrimes.primeBit p=1 <;> simp [h] <;> exact Or.inl rfl

def endpointSign (c : Named) (strict : Bool) := match c with
  | .robin => !strict
  | .nicolas => strict

def event (c : Named) (strict : Bool) (s m : Nat) : Prop :=
  let (lhs,rhs) := nativeParts c (endpointSign c strict) s m
  if strict then ltQ lhs rhs else leQ lhs rhs

private theorem excess_pos (x y : QPair) : excessQ x y ≠ 0 ↔ ltQ y x := by
  unfold excessQ ltQ; omega
private theorem excess_zero (x y : QPair) : excessQ x y = 0 ↔ leQ x y := by
  unfold excessQ leQ; omega

theorem margin_reading (c : Named) (strict : Bool) (s j : Nat) :
    (if strict then value (margin c strict) (pair s j) ≠ 0 else
      value (margin c strict) (pair s j) = 0) ↔ event c strict s (j+1) := by
  cases c <;> cases strict <;> unfold margin <;> rw [value_program] <;>
    simp only [Bool.false_eq_true,if_false,if_true,namedParts,readExcess,readBound,readMk,readSigma,readPrimeProd,
      Discrete.plus,excess_zero,excess_pos] <;> rfl

theorem strict_endpoints (c : Named) : naturalTerms.Holds (strictForm c) Fin.elim0 ↔
    ∀ s, ∃ j, event c true s (j+1) := by
  rw [strict_reading]
  exact forall_congr' (fun s => exists_congr (fun j => margin_reading c true s j))

theorem weak_endpoints (c : Named) : naturalTerms.Holds (weak c) Fin.elim0 ↔
    ∀ s j, event c false s (j+1) := by
  rw [weak,universal_reading]
  exact forall_congr' (fun s => forall_congr' (fun j => margin_reading c false s j))

def scaledEvent (side : Direction) (s m : Nat) : Prop :=
  let P := primorialNat false (s+3)
  let ratio := (P,primorialNat true (s+3))
  let bounded := fun a => leQ (timesQ (timesQ a a) (logNat false P m)) (25,1)
  let up := bounded (diffQ ratio (boundPair true P m))
  let lo := bounded (diffQ (boundPair false P m) ratio)
  match side with | .above => up | .below => lo | .both => up ∧ lo

theorem scaled_matrix_reading (d : Direction) (s j : Nat) :
    value (scaledMatrix d) (pair s j)=0 ↔ scaledEvent d s (j+1) := by
  cases d <;> unfold scaledMatrix <;> rw [value_program] <;>
    simp only [readExcess,readTimes,readDiff,readBound,readIntLog,readMk,readPrimeProd,
      Discrete.plus,Nat.add_eq_zero_iff,excess_zero] <;> rfl

theorem scaled_endpoints (d : Direction) : naturalTerms.Holds (scaled d) Fin.elim0 ↔
    ∀ s j, scaledEvent d s (j+1) := by
  rw [scaled,universal_reading]
  exact forall_congr' (fun s => forall_congr' (fun j => scaled_matrix_reading d s j))


private theorem product_pos (f : Nat → Nat) (n : Nat) (h : ∀ i < n, 0 < f i) :
    0 < overRange 1 (fun i a => a*f i) n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    exact Nat.mul_pos (ih fun i hi => h i (by omega)) (h n (by omega))

theorem commonNat_pos {a b m : Nat} (hb : 0 < b) : 0 < commonNat a b m := by
  apply product_pos
  intro i _
  exact Nat.add_pos_left hb _

theorem logPair_den (upper : Bool) {x : QPair} {m : Nat} (hx : 0 < x.2) (hm : 0 < m) :
    0 < (logPair upper x m).2 := commonNat_pos (Nat.mul_pos hx hm)

theorem logNat_den (upper : Bool) (n : Nat) {m : Nat} (hm : 0 < m) :
    0 < (logNat upper n m).2 :=
  Nat.mul_pos (Nat.mul_pos Nat.zero_lt_one (logPair_den upper Nat.zero_lt_one hm))
    (logPair_den upper (Nat.two_pow_pos _) hm)

theorem harmonicNum_le (m : Nat) : harmonicNum m ≤ m*m.factorial := by
  have h (n : Nat) :
      overRange 0 (fun j s => s+m.factorial/(j+1)) n ≤ n*m.factorial := by
    induction n with
    | zero => simp [overRange]
    | succ n ih =>
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih (Nat.div_le_self _ _)
  exact h m

theorem gammaPair_den (upper : Bool) {m : Nat} (hm : 0 < m) : 0 < (gammaPair upper m).2 := by
  have hf : 0 < m.factorial := Nat.factorial_pos _
  have hprod : 0 < m*m.factorial := Nat.mul_pos hm hf
  have hm2 : 2*m*m.factorial = m*m.factorial+m*m.factorial := by
    rw [Nat.two_mul, Nat.add_mul]
  have hdiff : harmonicNum m < 2*m*m.factorial := by
    have h := harmonicNum_le m
    omega
  cases upper
  · exact Nat.mul_pos (Nat.zero_lt_succ m) (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by decide) hm) hf))
  · exact Nat.mul_pos hm (Nat.pow_pos (Nat.sub_pos_of_lt hdiff))

theorem boundPair_den (upper : Bool) (n : Nat) {m : Nat} (hm : 0 < m) :
    0 < (boundPair upper n m).2 :=
  Nat.mul_pos (gammaPair_den upper hm) (logPair_den upper (logNat_den upper n hm) hm)

theorem primeProduct_pos (b : Bool) (y : Nat) : 0 < primorialNat b y := by
  apply product_pos
  intro i _
  by_cases h : SplitPrimes.primeBit i = 1
  · have hi := ((SplitPrimes.primeBit_iff i).mp h).1
    cases b <;> simp [h] <;> omega
  · simp [h]

theorem nativeParts_den (c : Named) (upper : Bool) (s : Nat) {m : Nat} (hm : 0 < m) :
    0 < (nativeParts c upper s m).1.2 ∧ 0 < (nativeParts c upper s m).2.2 := by
  cases c
  · exact ⟨by change 0<s+5041; omega, boundPair_den _ _ hm⟩
  · exact ⟨boundPair_den _ _ hm, primeProduct_pos true (s+3)⟩

def rational (x : QPair) : ℚ := (x.1 : ℚ) / x.2

theorem ltQ_rational (x y : QPair) (hx : 0 < x.2) (hy : 0 < y.2) :
    ltQ x y ↔ rational x < rational y := by
  unfold ltQ rational
  rw [div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  exact_mod_cast Iff.rfl

theorem leQ_rational (x y : QPair) (hx : 0 < x.2) (hy : 0 < y.2) :
    leQ x y ↔ rational x ≤ rational y := by
  unfold leQ rational
  rw [div_le_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  exact_mod_cast Iff.rfl

theorem event_rational (c : Named) (strict : Bool) (s : Nat) {m : Nat} (hm : 0 < m) :
    event c strict s m ↔
      let pr := nativeParts c (endpointSign c strict) s m
      if strict then rational pr.1 < rational pr.2 else rational pr.1 ≤ rational pr.2 := by
  have h := nativeParts_den c (endpointSign c strict) s hm
  cases strict
  · exact leQ_rational _ _ h.1 h.2
  · exact ltQ_rational _ _ h.1 h.2


theorem strict_rational_reading (c : Named) : naturalTerms.Holds (strictForm c) Fin.elim0 ↔
    ∀ s, ∃ j, let pr := nativeParts c (endpointSign c true) s (j+1)
              rational pr.1 < rational pr.2 := by
  rw [strict_endpoints]
  exact forall_congr' (fun s => exists_congr (fun j => event_rational c true s (Nat.zero_lt_succ j)))

theorem weak_rational_reading (c : Named) : naturalTerms.Holds (weak c) Fin.elim0 ↔
    ∀ s j, let pr := nativeParts c (endpointSign c false) s (j+1)
           rational pr.1 ≤ rational pr.2 := by
  rw [weak_endpoints]
  exact forall_congr' (fun s => forall_congr' (fun j => event_rational c false s (Nat.zero_lt_succ j)))

theorem rational_times (x y : QPair) : rational (timesQ x y) = rational x * rational y := by
  simp only [rational,timesQ,Nat.cast_mul,div_mul_div_comm]

theorem rational_diff (x y : QPair) (hx : 0 < x.2) (hy : 0 < y.2) :
    rational (diffQ x y) = max 0 (rational x-rational y) := by
  have hx' : (x.2 : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hy' : (y.2 : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  by_cases h : y.1*x.2 ≤ x.1*y.2
  · have hr := (leQ_rational y x hy hx).mp h
    rw [max_eq_right (sub_nonneg.mpr hr)]
    simp only [rational,diffQ,excessQ,Nat.cast_sub h,Nat.cast_mul]
    field_simp
  · have h' : x.1*y.2 ≤ y.1*x.2 := by omega
    have hr := (leQ_rational x y hx hy).mp h'
    rw [max_eq_left (sub_nonpos.mpr hr)]
    simp only [rational,diffQ,excessQ,Nat.sub_eq_zero_of_le h',Nat.cast_zero,zero_div]

def scaledRational (side : Direction) (s m : Nat) : Prop :=
  let P := primorialNat false (s+3)
  let ratio := rational (P,primorialNat true (s+3))
  let L := rational (logNat false P m)
  let up := (max 0 (ratio-rational (boundPair true P m)))^2 * L ≤ 25
  let lo := (max 0 (rational (boundPair false P m)-ratio))^2 * L ≤ 25
  match side with | .above => up | .below => lo | .both => up ∧ lo

theorem scaledEvent_rational (side : Direction) (s : Nat) {m : Nat} (hm : 0 < m) :
    scaledEvent side s m ↔ scaledRational side s m := by
  let P := primorialNat false (s+3)
  let ratio : QPair := (P,primorialNat true (s+3))
  have hr : 0 < ratio.2 := primeProduct_pos true (s+3)
  have eval (a b : QPair) (ha : 0 < a.2) (hb : 0 < b.2) :
      leQ (timesQ (timesQ (diffQ a b) (diffQ a b)) (logNat false P m)) (25,1) ↔
      (max 0 (rational a-rational b))^2 * rational (logNat false P m) ≤ 25 := by
    have hd : 0 < (diffQ a b).2 := Nat.mul_pos ha hb
    rw [leQ_rational _ _ (Nat.mul_pos (Nat.mul_pos hd hd) (logNat_den _ _ hm)) Nat.zero_lt_one]
    simp only [rational_times,rational_diff a b ha hb,pow_two]
    norm_num [rational]
  have up := eval ratio (boundPair true P m) hr (boundPair_den _ _ hm)
  have lo := eval (boundPair false P m) ratio (boundPair_den _ _ hm) hr
  cases side
  · exact up
  · exact lo
  · exact and_congr up lo

theorem scaled_rational_reading (d : Direction) : naturalTerms.Holds (scaled d) Fin.elim0 ↔
    ∀ s j, scaledRational d s (j+1) := by
  rw [scaled_endpoints]
  exact forall_congr' (fun s => forall_congr' (fun j => scaledEvent_rational d s (Nat.zero_lt_succ j)))

theorem scheduled (c : Named) (g : PR 1) : Prf PRAAx []
    (Fm.iff (weak c) ((UniversalCriteria.block (weak c)).schedule g)) :=
  UniversalCriteria.scheduled (.binder (.binder (.matrix _))) g

theorem scaled_scheduled (d : Direction) (g : PR 1) : Prf PRAAx []
    (Fm.iff (scaled d) ((UniversalCriteria.block (scaled d)).schedule g)) :=
  UniversalCriteria.scheduled (.binder (.binder (.matrix _))) g

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.RobinNicolas
