import IPRADerivations.AnalyticNumberTheory.Riemann.DiscreteForms
import IPRADerivations.AnalyticNumberTheory.Riemann.PrimeForms

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`SplitPrimes.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! One reduced residue class, and primes where a coded polynomial splits
completely. Every prime contributes its first power only. -/
set_option maxRecDepth 4096
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.SplitPrimes
open LeanProofs.ConciseIPRA PacketLanguage Discrete

private def ztest {c} (a : E c) := call isZeroR [a]
private def isPrimeE {c} (p : E c) := eqB (call primeCode [p]) 1

/-- Polynomial data use the actual degree, with leading monomial implicit. -/
def polynomialSplit : PR 5 := program ["d","H","u","v","p"] <|
  ztest (sumTo "j" (v "d"-1) <|
    sumTo "a" (powE (v "p") (v "j"+2)) <|
      let f := call PacketPolynomial.residueWord [v "d",v "H",v "u",v "v",v "p"]
      let k := v "j"+2
      call PacketPolynomial.irred [v "p",k,v "a"] *
        call PacketPolynomial.divides [v "p",k,v "a",v "d",f])

/-- The progression modulus is always at least two in the closed sentences. -/
def progressionLog : PR 2 := program ["m","y"] <|
  call logCode [prodTo "p" (v "y"+1) (iteE
    (isPrimeE (v "p") * eqB (modE (v "p") (v "m")) 1) (v "p") 1)]

def splitLog : PR 5 := program ["d","H","u","v","y"] <|
  call logCode [prodTo "p" (v "y"+1) (iteE
    (isPrimeE (v "p") * call polynomialSplit [v "d",v "H",v "u",v "v",v "p"])
    (v "p") 1)]

private def dist {c} (a b : E c) := (a-b)+(b-a)
private def lengthE {c} (x : E c) := 1+call logCode [x]

def progGap : PR 2 := program ["m","n"] <| dist
    (call progressionLog [v "m",2*v "n"]) (2*call progressionLog [v "m",v "n"])

inductive Schedule where | ordinary | factorial

private def chooseMod {c} (s : Schedule) (d : E c) := match s with
  | .ordinary => d+2
  | .factorial => call PrimeForms.factCode [d+2]

def progMatrix (s : Schedule) : PR 5 := program ["d0","H","u","v","t"] <|
  let n := v "t"+100
  let m := chooseMod s (v "d0")
  powE (call progGap [m,n]) 2 - n * powE (64 * powE (lengthE (2*n)) 2) 2

/-- For n=t+100 the loop covers m=2,3,...,2n; every larger modulus gives
an empty prime product at both n and 2n. -/
def maxMatrix : PR 5 := program ["d0","H","u","v","t"] <|
  let n := v "t"+100
  let largest := maxTo "j" (2*n-1) (call progGap [v "j"+2,v "t"+100])
  powE largest 2 - n * powE (64 * powE (lengthE (2*n)) 2) 2

def fieldMatrix : PR 5 := program ["d0","H","u","v","t"] <|
  let d := v "d0"+1
  let n := v "t"+100
  let f := call PrimeForms.factCode [d]
  let R := d*(v "H"+2)*powE (1+d*powE f 2) d
  let K := 128*(1+2*f*R+2*powE d 2*(v "H"+2))
  let B := fun y => call splitLog [d,v "H",v "u",v "v",y]
  powE (dist (B (2*n)) (2*B n)) 2 - n * powE (K*powE (lengthE (2*n)) 2) 2

/-- Operational unary field criterion. Each of the four polynomial codes runs
from zero through the current binary length. The normalized discriminant
allowance is checked before selecting its gap. -/
def unaryFieldMatrix : PR 5 := program ["d0","H","u","v","t"] <|
  let n := v "t"+100
  let largest := maxTo "di" (lengthE (2*n)+1) <|
    maxTo "hi" (lengthE (2*(v "t"+100))+1) <|
    maxTo "ui" (lengthE (2*(v "t"+100))+1) <|
    maxTo "vi" (lengthE (2*(v "t"+100))+1) <|
      let n := v "t"+100
      let d := v "di"+1
      let f := call PrimeForms.factCode [d]
      let R := d*(v "hi"+2)*powE (1+d*powE f 2) d
      let A := 1+2*f*R+2*powE d 2*(v "hi"+2)
      let B := fun y => call splitLog [d,v "hi",v "ui",v "vi",y]
      leB A (lengthE (2*n)) * dist (B (2*n)) (2*B n)
  powE largest 2 - n * powE (64*powE (lengthE (2*n)) 2) 2

def unaryERH := Family.riemann.close unaryFieldMatrix

def RH := Family.riemann.close (progMatrix .ordinary)
def GRH (s : Schedule) := Family.dirichlet.close (progMatrix s)
def unaryGRH := Family.riemann.close maxMatrix
def ERH := Family.dedekind.close fieldMatrix

-- Arithmetic readings of the local factors and whole matrices.
private def arg2 (a b : Nat) : Fin 2 → Nat := Fin.cases a (fun _ => b)
private theorem read2 {c} (f : PR 2) (a b : E c) (e) :
    denote (call f [a,b]) e = value f (arg2 (denote a e) (denote b e)) := by
  apply congrArg (value f)
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun i => i.elim0) j) i

private theorem read1 {c} (f : PR 1) (x : E c) (e) :
    denote (call f [x]) e = value f (fun _ => denote x e) := by
  apply congrArg (value f)
  funext i
  exact Fin.cases rfl (fun i => i.elim0) i

private theorem readLog {c} (x : E c) (e) :
    denote (call logCode [x]) e = (denote x e).log2 := by rw [read1, value_logCode]
private theorem readZero {c} (x : E c) (e) :
    denote (ztest x) e = (if denote x e = 0 then 1 else 0) := by
  unfold ztest; rw [read1,value_isZeroR]
private theorem readLe {c} (a b : E c) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  unfold leB; rw [read1, value_isZeroR]
  simp only [minus,Nat.sub_eq_zero_iff_le]
private theorem readEq {c} (a b : E c) (e) :
    denote (eqB a b) e = (if denote a e = denote b e then 1 else 0) := by
  simp only [eqB,times,readLe]
  split <;> split <;> split <;> first | rfl | omega
private theorem readIte {c} (t a b : E c) (e) :
    denote (iteE t a b) e = (if denote t e=0 then denote b e else denote a e) := by
  simp only [iteE,plus,times,read1,value_isZeroR,value_clipR,bit]
  split <;> simp_all
private theorem readSum {c} (j : String) (N : E c) (s : E (j::c)) (e) :
    denote (sumTo j N s) e = total (fun i => denote s (Fin.cases i e)) (denote N e) := by
  change overRange 0 _ _ = _
  generalize denote N e = n
  induction n with | zero => rfl | succ n ih => exact congrArg (·+_) ih

def prod (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => prod f n * f n

private theorem readProd {c} (j : String) (N : E c) (s : E (j::c)) (e) :
    denote (prodTo j N s) e = prod (fun i => denote s (Fin.cases i e)) (denote N e) := by
  change overRange 1 _ _ = _
  generalize denote N e = n
  induction n with | zero => rfl | succ n ih => exact congrArg (·*_) ih

def peak (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => max (peak f n) (f n)

private theorem readMax {c} (j : String) (N : E c) (s : E (j::c)) (e) :
    denote (maxTo j N s) e = peak (fun i => denote s (Fin.cases i e)) (denote N e) := by
  change overRange 0 _ _ = _
  generalize denote N e = n
  induction n with | zero => rfl | succ n ih => exact congrArg (fun x => max x _) ih

/-- Native arithmetic reading of the factor search. -/
def obstruction (d H u v p j a : Nat) : Nat :=
  value PacketPolynomial.irred (args3 p (j+2) a) *
    value PacketPolynomial.divides (packetArgs p (j+2) a d
      (value PacketPolynomial.residueWord (packetArgs d H u v p)))

def localBit (d H u v p : Nat) : Nat :=
  if total (fun j => total (obstruction d H u v p j) (p^(j+2))) (d-1) = 0 then 1 else 0

theorem split_reading (d H u v p : Nat) :
    value polynomialSplit (packetArgs d H u v p) = localBit d H u v p := by
  unfold polynomialSplit; rw [value_program,readZero]
  simp only [readSum,times,minus,plus,power,apply3,apply5]; rfl

private theorem total_zero (f : Nat → Nat) (n : Nat) :
    total f n = 0 ↔ ∀ i < n, f i = 0 := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total, Nat.add_eq_zero_iff, ih]
    constructor
    · rintro ⟨h,h'⟩ i hi
      by_cases he : i=n
      · simpa [he] using h'
      · exact h i (by omega)
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem split_iff (d H u v p : Nat) : value polynomialSplit (packetArgs d H u v p) = 1 ↔
    ∀ j < d-1, ∀ a < p^(j+2), obstruction d H u v p j a = 0 := by
  rw [split_reading]; unfold localBit
  have test (z : Nat) : (if z = 0 then 1 else 0 : Nat) = 1 ↔ z = 0 := by cases z <;> simp
  rw [test]
  simp only [total_zero]

def primeBit (p : Nat) := value primeCode (fun _ => p)
theorem primeBit_iff (p : Nat) : primeBit p = 1 ↔
    2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0 := value_primeCode _

def progressionFactor (m p : Nat) := if primeBit p = 1 ∧ p % m = 1 then p else 1
def fieldFactor (d H u v p : Nat) := if primeBit p = 1 ∧ localBit d H u v p = 1 then p else 1

def progB (m y : Nat) := (prod (progressionFactor m) (y+1)).log2
def fieldB (d H u v y : Nat) := (prod (fieldFactor d H u v) (y+1)).log2

theorem progression_reading (m y : Nat) : value progressionLog (arg2 m y) = progB m y := by
  unfold progressionLog progB; rw [value_program,readLog,readProd]
  simp only [readIte,times,isPrimeE,readEq,denote_modE,read1,plus]
  apply congrArg Nat.log2
  apply congrArg (fun f => prod f (y+1))
  funext p
  change (if (if primeBit p=1 then 1 else 0)*(if p%m=1 then 1 else 0)=0 then 1 else p) = _
  by_cases h : primeBit p=1 <;> by_cases h' : p%m=1 <;> simp [h,h',progressionFactor]

theorem field_reading (d H u v y : Nat) :
    value splitLog (packetArgs d H u v y) = fieldB d H u v y := by
  unfold splitLog fieldB; rw [value_program,readLog,readProd]
  simp only [readIte,times,isPrimeE,readEq,read1,plus,apply5]
  apply congrArg Nat.log2
  apply congrArg (fun f => prod f (y+1))
  funext p
  change (if (if primeBit p=1 then 1 else 0)*value polynomialSplit (packetArgs d H u v p)=0 then 1 else p) = _
  rw [split_reading]
  by_cases h : primeBit p=1 <;> by_cases h' : total (fun j => total (obstruction d H u v p j)
    (p^(j+2))) (d-1)=0 <;> simp [fieldFactor,localBit,h,h']

def gap (m n : Nat) := delta (progB m (2*n)) (2*progB m n)
theorem gap_reading (m n : Nat) : value progGap (arg2 m n) = gap m n := by
  unfold progGap; rw [value_program]
  simp only [dist,plus,minus,times,read2,progression_reading]; rfl

def factorial (n : Nat) := prod (·+1) n
private theorem readFact {c} (t : E c) (e) :
    denote (call PrimeForms.factCode [t]) e = factorial (denote t e) := by
  rw [read1]; unfold PrimeForms.factCode; rw [value_program,readProd]
  simp only [plus]; rfl

def Schedule.modulus (s : Schedule) (i : Nat) := match s with
  | .ordinary => i+2 | .factorial => SplitPrimes.factorial (i+2)

def budget (n : Nat) := n * (64 * (1+(2*n).log2)^2)^2
def fieldBudget (d H n : Nat) :=
  let R := d*(H+2)*(1+d*(factorial d)^2)^d
  let K := 128*(1+2*factorial d*R+2*d^2*(H+2))
  n*(K*(1+(2*n).log2)^2)^2

theorem prog_matrix_reading (s : Schedule) (p : Data) (t : Nat) :
    value (progMatrix s) (p.args t) = 0 ↔
      (gap (s.modulus p.degreeOffset) (t+100))^2 ≤ budget (t+100) := by
  cases s <;> unfold progMatrix <;> rw [value_program,minus,Nat.sub_eq_zero_iff_le]
  all_goals simp only [chooseMod,lengthE,plus,times,power,readLog,read2,gap_reading,readFact]; rfl

theorem max_matrix_reading (p : Data) (t : Nat) :
    value maxMatrix (p.args t) = 0 ↔
      (peak (fun j => gap (j+2) (t+100)) (2*(t+100)-1))^2 ≤ budget (t+100) := by
  unfold maxMatrix; rw [value_program,minus,Nat.sub_eq_zero_iff_le]
  simp only [readMax,lengthE,plus,times,power,minus,readLog,read2,gap_reading]; rfl

theorem field_matrix_reading (p : Data) (t : Nat) :
    value fieldMatrix (p.args t) = 0 ↔
      (delta (fieldB (p.degreeOffset+1) p.height p.pos p.neg (2*(t+100)))
        (2*fieldB (p.degreeOffset+1) p.height p.pos p.neg (t+100)))^2 ≤
      fieldBudget (p.degreeOffset+1) p.height (t+100) := by
  unfold fieldMatrix; rw [value_program,minus,Nat.sub_eq_zero_iff_le]
  simp only [dist,lengthE,plus,minus,times,power,readLog,apply5,field_reading,readFact]; rfl

private theorem read_family (s : Family) (f : PR 5) (P : Data → Nat → Prop)
    (h : ∀ p t, value f (p.args t)=0 ↔ P p t) :
    naturalTerms.Holds (s.close f) Fin.elim0 ↔ s.allData (fun p => ∀ t, P p t) :=
  (s.holds_matrix f).trans (s.lift_iff (fun p => forall_congr' (h p)))

theorem rh_reading : naturalTerms.Holds RH Fin.elim0 ↔
    ∀ t, (gap 2 (t+100))^2 ≤ budget (t+100) :=
  read_family _ _ _ (prog_matrix_reading .ordinary)

theorem grh_reading (s : Schedule) : naturalTerms.Holds (GRH s) Fin.elim0 ↔
    ∀ i t, (gap (s.modulus i) (t+100))^2 ≤ budget (t+100) :=
  read_family _ _ _ (prog_matrix_reading s)

theorem unary_reading : naturalTerms.Holds unaryGRH Fin.elim0 ↔
    ∀ t, (peak (fun j => gap (j+2) (t+100)) (2*(t+100)-1))^2 ≤ budget (t+100) :=
  read_family _ _ _ max_matrix_reading

theorem erh_reading : naturalTerms.Holds ERH Fin.elim0 ↔
    ∀ i H u v t, (delta (fieldB (i+1) H u v (2*(t+100))) (2*fieldB (i+1) H u v (t+100)))^2 ≤
      fieldBudget (i+1) H (t+100) :=
  read_family _ _ _ field_matrix_reading

def rootAllowance (d H : Nat) :=
  let f := factorial d
  let R := d*(H+2)*(1+d*f^2)^d
  1+2*f*R+2*d^2*(H+2)

def restrictedFieldPeak (n : Nat) :=
  let L := 1+(2*n).log2
  peak (fun i => peak (fun H => peak (fun u => peak (fun v =>
    (if rootAllowance (i+1) H ≤ L then 1 else 0) *
      delta (fieldB (i+1) H u v (2*n)) (2*fieldB (i+1) H u v n)) (L+1)) (L+1)) (L+1)) (L+1)

theorem unary_field_matrix_reading (p : Data) (t : Nat) :
    value unaryFieldMatrix (p.args t) = 0 ↔
    (restrictedFieldPeak (t+100))^2 ≤ budget (t+100) := by
  unfold unaryFieldMatrix; rw [value_program,minus,Nat.sub_eq_zero_iff_le]
  simp only [dist,readMax,readLe,lengthE,plus,minus,times,power,readLog,apply5,field_reading,readFact]
  rfl

theorem unary_erh_reading : naturalTerms.Holds unaryERH Fin.elim0 ↔
    ∀ t, (restrictedFieldPeak (t+100))^2 ≤ budget (t+100) :=
  read_family _ _ _ unary_field_matrix_reading

theorem prog_grh_to_rh : Prf PRAAx [] (.imp (GRH .ordinary) RH) :=
  RHHierarchy.grh_implies_rh _

private theorem prod_ones (f : Nat → Nat) (n : Nat) (h : ∀ p < n, f p = 1) : prod f n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prod, h n (by omega), ih (fun p hp => h p (by omega))]

theorem large_modulus {m y : Nat} (h : y < m) : progB m y = 0 := by
  unfold progB
  rw [prod_ones (progressionFactor m) (y+1)]
  · decide
  · intro p hp
    have hm : p < m := by omega
    unfold progressionFactor; rw [Nat.mod_eq_of_lt hm]
    by_cases hq : primeBit p = 1
    · have hge := ((primeBit_iff p).mp hq).1
      have hn : p ≠ 1 := by omega
      simp [hn]
    · simp [hq]

theorem large_modulus_gap {m n : Nat} (h : 2*n < m) : gap m n = 0 := by
  unfold gap
  rw [large_modulus h, large_modulus (show n < m by omega)]
  rfl

private theorem peak_sq_le (f : Nat → Nat) (n K : Nat) :
    (peak f n)^2 ≤ K ↔ ∀ j < n, (f j)^2 ≤ K := by
  induction n with
  | zero => simp [peak]
  | succ n ih =>
    have hmax (a b : Nat) : (max a b)^2 ≤ K ↔ a^2 ≤ K ∧ b^2 ≤ K := by
      rcases Nat.le_total a b with h | h
      · rw [Nat.max_eq_right h]
        exact ⟨fun hh => ⟨(Nat.pow_le_pow_left h _).trans hh,hh⟩,And.right⟩
      · rw [Nat.max_eq_left h]
        exact ⟨fun hh => ⟨hh,(Nat.pow_le_pow_left h _).trans hh⟩,And.left⟩
    rw [peak,hmax,ih]
    constructor
    · rintro ⟨h,h'⟩ i hi
      by_cases he : i=n
      · simpa [he] using h'
      · exact h i (by omega)
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- The unary maximum preserves the ordinary progression criterion by a purely
finite argument for each cutoff. -/
theorem unary_grh_iff : naturalTerms.Holds unaryGRH Fin.elim0 ↔
    naturalTerms.Holds (GRH .ordinary) Fin.elim0 := by
  rw [unary_reading,grh_reading]
  constructor
  · intro h i t
    change (gap (i+2) (t+100))^2 ≤ _
    by_cases hi : i < 2*(t+100)-1
    · exact (peak_sq_le _ _ _).mp (h t) i hi
    · rw [large_modulus_gap (show 2*(t+100)<i+2 by omega)]
      simp
  · intro h t
    exact (peak_sq_le _ _ _).mpr (fun i _ => h i t)

/-- Every monic linear polynomial splits, including at primes dividing the
constant coefficient. -/
theorem linear_splits (H u v p : Nat) : value polynomialSplit (packetArgs 1 H u v p) = 1 :=
  (split_iff ..).mpr (fun j h => by omega)

private theorem linear_factor (H u v p : Nat) :
    fieldFactor 1 H u v p = if primeBit p=1 then p else 1 := by
  have h := linear_splits H u v p
  rw [split_reading] at h
  simp [fieldFactor,h]

private theorem odd_factor_positive (p : Nat) : 0 < progressionFactor 2 p := by
  unfold progressionFactor
  split
  · rename_i h; have := ((primeBit_iff p).mp h.1).1; omega
  · decide

private theorem odd_product_positive (n : Nat) : 0 < prod (progressionFactor 2) n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos ih (odd_factor_positive n)

private theorem linear_ratio (H u v j : Nat) :
    prod (fieldFactor 1 H u v) (j+3) = 2 * prod (progressionFactor 2) (j+3) := by
  induction j with
  | zero =>
    have h0 : primeBit 0 ≠ 1 := fun h => by have := ((primeBit_iff _).mp h).1; omega
    have h1 : primeBit 1 ≠ 1 := fun h => by have := ((primeBit_iff _).mp h).1; omega
    have h2 : primeBit 2 = 1 := (primeBit_iff _).mpr ⟨by decide,fun d h h' => by omega⟩
    simp [prod,linear_factor,progressionFactor,h0,h1,h2]
  | succ j ih =>
    let p := j+3
    have atp : fieldFactor 1 H u v p = progressionFactor 2 p := by
      rw [linear_factor]; unfold progressionFactor
      by_cases h : primeBit p=1
      · have hm := ((primeBit_iff _).mp h).2 2 (by decide) (by dsimp [p]; omega)
        have h1 : p%2=1 := by omega
        simp [h,h1]
      · simp [h]
    change prod _ (j+3)*fieldFactor 1 H u v p = 2*(prod _ (j+3)*progressionFactor 2 p)
    rw [ih,atp,Nat.mul_assoc]

/-- Above the prime two the bit-log of a linear input differs from the odd
prime bit-log by exactly one. -/
theorem linear_field_log (H u v y : Nat) (hy : 2 ≤ y) :
    fieldB 1 H u v y = progB 2 y + 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hy
  unfold fieldB progB
  have e : 2+j+1=j+3 := by omega
  rw [e,linear_ratio,Nat.log2_two_mul (Nat.ne_of_gt (odd_product_positive _))]

open Smoke in
#guard vecEval polynomialSplit #v[2,0,1,0,2] == 1  -- X²+1 = (X+1)² modulo 2.
open Smoke in
#guard vecEval polynomialSplit #v[2,0,3,0,2] == 0  -- X²+X+1 is irreducible modulo 2.

/-! Evaluate the underlying finite-field test without leaving any imported
opaque PR symbols in its arithmetic specification. -/
private def rep4 (a b c d : Nat) : Fin 4 → Nat :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private def rep6 (a b c d e f : Nat) : Fin 6 → Nat :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (fun _ => f)))))

private theorem read4 {c} (g : PR 4) (a b x y : E c) (e) :
    denote (call g [a,b,x,y]) e = value g (rep4 (denote a e) (denote b e) (denote x e) (denote y e)) := by
  apply congrArg (value g); funext ⟨i,hi⟩
  match i with | 0 | 1 | 2 | 3 => rfl | k+4 => omega

private theorem read6 {c} (g : PR 6) (a b x y z t : E c) (e) :
    denote (call g [a,b,x,y,z,t]) e = value g
      (rep6 (denote a e) (denote b e) (denote x e) (denote y e) (denote z e) (denote t e)) := by
  apply congrArg (value g); funext ⟨i,hi⟩
  match i with | 0 | 1 | 2 | 3 | 4 | 5 => rfl | k+6 => omega

def every (f : Nat → Nat) := overRange 1 (fun i a => a * bit (f i))
def someEntry (f : Nat → Nat) := overRange 0 (fun i a => bit (a + f i))
private theorem readEvery {c} (j : String) (n : E c) (s : E (j::c)) (e) :
    denote (allTo j n s) e = every (fun i => denote s (Fin.cases i e)) (denote n e) := rfl
private theorem readSome {c} (j : String) (n : E c) (s : E (j::c)) (e) :
    denote (anyTo j n s) e = someEntry (fun i => denote s (Fin.cases i e)) (denote n e) := rfl
private theorem readDigit {c} (w b i : E c) (e) :
    denote (digitE w b i) e = (denote w e / (denote b e)^(denote i e)) % denote b e := by
  unfold digitE
  rw [denote_modE,denote_divE]
  change _ / denote (powE b i) e % _ = _; rw [power]

def digit (w b i : Nat) := w/b^i%b
def reduction (d H u v p : Nat) :=
  total (fun i => ((digit u (H+2) i + p - digit v (H+2) i % p) % p)*p^i) d
def coeff (p d w j : Nat) := if j=d then 1 else if j<d then digit w p j else 0
def multiplicationBit (p e a h b w : Nat) := every (fun j =>
  if total (fun i => coeff p e a i * coeff p h b (j-i)) (j+1) % p =
    coeff p (e+h) w j then 1 else 0) (e+h+1)
def divisorBit (p e a d w : Nat) := (if e≤d then 1 else 0) *
  someEntry (fun b => multiplicationBit p e a (d-e) b w) (p^(d-e))
def irredBit (p e a : Nat) := (if 1≤e then 1 else 0) * every (fun t =>
  every (fun b => if divisorBit p (t+1) b e a=0 then 1 else 0) (p^(t+1))) (e-1)

theorem reduction_reading (d H u v p : Nat) :
    value PacketPolynomial.residueWord (packetArgs d H u v p) = reduction d H u v p := by
  unfold PacketPolynomial.residueWord
  rw [value_program,readSum]; simp only [times,denote_modE,minus,plus,readDigit,power]; rfl

private theorem coeff_reading (p d w j : Nat) :
    value PacketPolynomial.monicAt (rep4 p d w j) = coeff p d w j := by
  unfold PacketPolynomial.monicAt
  rw [value_program]
  simp only [readIte,readEq,readLe,plus,readDigit]
  change (if (if j=d then 1 else 0)=0 then
    (if (if j+1≤d then 1 else 0)=0 then 0 else digit w p j) else 1) = _
  by_cases hj : j=d <;> by_cases hj' : j<d <;> simp [coeff,hj,Nat.succ_le_iff,hj']

theorem multiplication_reading (p e a h b w : Nat) :
    value PacketPolynomial.productEquals (rep6 p e a h b w) = multiplicationBit p e a h b w := by
  unfold PacketPolynomial.productEquals
  rw [value_program,readEvery]
  simp only [readEq,denote_modE,readSum,times,plus,minus,read4,coeff_reading]; rfl

theorem divisor_reading (p e a d w : Nat) :
    value PacketPolynomial.divides (packetArgs p e a d w) = divisorBit p e a d w := by
  unfold PacketPolynomial.divides
  rw [value_program,times,readLe,readSome]
  simp only [power,minus,read6,multiplication_reading]; rfl

theorem irred_reading (p e a : Nat) :
    value PacketPolynomial.irred (args3 p e a) = irredBit p e a := by
  unfold PacketPolynomial.irred
  rw [value_program,times,readLe,readEvery]
  simp only [readEvery,minus,power,plus,readEq,apply5,divisor_reading]; rfl

/-- Arithmetic denotation down to the base-p digits of the monic factors
and candidate quotients. The field-theoretic factorization argument is in
the report. -/
theorem split_iff_coefficients (d H u v p : Nat) :
    value polynomialSplit (packetArgs d H u v p)=1 ↔
    ∀ j < d-1, ∀ a < p^(j+2),
      irredBit p (j+2) a * divisorBit p (j+2) a d (reduction d H u v p) = 0 := by
  rw [split_iff]; simp only [obstruction,irred_reading,divisor_reading,reduction_reading]

private theorem every_nonzero (f : Nat → Nat) (n : Nat) :
    every f n ≠ 0 ↔ ∀ i < n, f i ≠ 0 := by
  induction n with
  | zero => simp [every,overRange]
  | succ n ih =>
    change every f n * bit (f n) ≠ 0 ↔ _
    have hb : bit (f n) ≠ 0 ↔ f n ≠ 0 := by cases f n <;> simp [bit]
    rw [Nat.mul_ne_zero_iff, hb, ih]
    constructor
    · rintro ⟨h,h'⟩ i hi
      by_cases he : i=n
      · simpa [he] using h'
      · exact h i (by omega)
    · intro h; exact ⟨fun i hi => h i (by omega),h n (by omega)⟩

private theorem some_nonzero (f : Nat → Nat) (n : Nat) :
    someEntry f n ≠ 0 ↔ ∃ i < n, f i ≠ 0 := by
  induction n with
  | zero => simp [someEntry,overRange]
  | succ n ih =>
    change bit (someEntry f n + f n) ≠ 0 ↔ _
    have hb (a b : Nat) : bit (a+b) ≠ 0 ↔ a≠0 ∨ b≠0 := by
      cases a <;> cases b <;> simp [bit]
    rw [hb,ih]
    constructor
    · rintro (⟨i,hi,h⟩ | hn)
      · exact ⟨i,by omega,h⟩
      · exact ⟨n,by omega,hn⟩
    · rintro ⟨i,hi,h⟩
      by_cases he : i=n
      · exact Or.inr (he ▸ h)
      · exact Or.inl ⟨i,by omega,h⟩

def productMatches (p e a h b w : Nat) : Prop := ∀ j < e+h+1,
    total (fun i => coeff p e a i * coeff p h b (j-i)) (j+1) % p = coeff p (e+h) w j

def isDivisor (p e a d w : Nat) : Prop := e≤d ∧ ∃ b < p^(d-e), productMatches p e a (d-e) b w

def isIrred (p e a : Nat) : Prop := 1≤e ∧ ∀ t < e-1, ∀ b < p^(t+1), ¬isDivisor p (t+1) b e a

private theorem if_nonzero (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) ≠ 0 ↔ P := by
  by_cases h : P <;> simp [h]

private theorem productMatches_iff (p e a h b w : Nat) :
    multiplicationBit p e a h b w ≠ 0 ↔ productMatches p e a h b w := by
  simp only [multiplicationBit,every_nonzero,if_nonzero,productMatches]

private theorem isDivisor_iff (p e a d w : Nat) :
    divisorBit p e a d w ≠ 0 ↔ isDivisor p e a d w := by
  simp only [divisorBit,Nat.mul_ne_zero_iff,if_nonzero,some_nonzero,productMatches_iff,isDivisor]

private theorem isIrred_iff (p e a : Nat) : irredBit p e a ≠ 0 ↔ isIrred p e a := by
  have h (m g x y z : Nat) : divisorBit m g x y z=0 ↔ ¬isDivisor m g x y z := by
    constructor
    · intro hz h
      exact (isDivisor_iff ..).mpr h hz
    · intro hn
      by_cases hh : divisorBit m g x y z=0
      · exact hh
      · exact False.elim (hn ((isDivisor_iff ..).mp hh))
  simp only [irredBit,Nat.mul_ne_zero_iff,if_nonzero,every_nonzero,h,isIrred]

theorem split_iff_no_irred_divisor (d H u v p : Nat) :
    value polynomialSplit (packetArgs d H u v p)=1 ↔
    ∀ j < d-1, ∀ a < p^(j+2), isIrred p (j+2) a →
      ¬isDivisor p (j+2) a d (reduction d H u v p) := by
  rw [split_iff_coefficients]
  constructor
  · intro h j hj a ha hi hd
    exact (Nat.mul_ne_zero ((isIrred_iff ..).mpr hi) ((isDivisor_iff ..).mpr hd)) (h j hj a ha)
  · intro h j hj a ha
    by_cases hi : irredBit p (j+2) a = 0
    · simp [hi]
    · have hn := h j hj a ha ((isIrred_iff ..).mp hi)
      by_cases hd : divisorBit p (j+2) a d (reduction d H u v p)=0
      · simp [hd]
      · exact False.elim (hn ((isDivisor_iff ..).mp hd))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.SplitPrimes
