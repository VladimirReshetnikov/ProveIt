import IPRADerivations.AnalyticNumberTheory.Riemann.DiscreteSyntax
import IPRADerivations.AnalyticNumberTheory.Riemann.PrimeForms

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`TaylorPackets.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Finite integer certificates for the Taylor radii of a pole-cancelled
Dirichlet series. Each schedule yields one closed sentence for each family. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.Taylor
open LeanProofs.ConciseIPRA PacketLanguage Discrete

/-- J(n,h)/h² approximates the natural logarithm from below for n,h ≥ 1. -/
def logNumerator : PR 2 := program ["n","h"] <|
  sumTo "i" (v "h" * (v "n"-1)) (divE (v "h" * v "h") (v "h"+v "i"+1))

/-- A signed sum is stored as two nonnegative sums. c is the actual centre. -/
def numerator (negative : Bool) : PR 7 := program ["d","H","u","v","c","k","N"] <|
  sumTo "i" (v "N") <|
    let n := v "i"+1
    let B := fun x => call logProduct [v "d"+1,v "H",v "u",v "v",x]
    let jump := if negative then 2 * (B (divE n 2) - B (divE (v "i") 2))
                else B n - B (v "i")
    let logWeight := powE (call logNumerator [n,v "N"]) (v "k")
    let dirichletWeight := powE (divE (call PrimeForms.factCode [v "N"]) n) (v "c")
    jump * logWeight * dirichletWeight

inductive Schedule where | allDisks | diagonal | lacunary

private def centre {ctx} (mode : Schedule) (i : E ctx) : E ctx :=
  match mode with
  | .allDisks | .diagonal => i+5
  | .lacunary => powE 2 i+4

private def index {ctx} (mode : Schedule) (c j : E ctx) : E ctx :=
  match mode with
  | .allDisks => j+1
  | .diagonal | .lacunary => c

/-- Raw input (degree offset, height, two polynomial words, centre index,
radius index, Taylor order, precision offset). -/
def matrix (mode : Schedule) : PR 8 := program ["d","H","u","v","i","j","k","t"] <|
  let c := centre mode (v "i")
  let j := index mode c (v "j")
  let k := v "k"
  let N := v "t"+1
  let d := v "d"+1
  let P := (2*c-1)*j-1
  let Q := 2*j
  let C := 1000*powE (d+1) 4*powE (v "H"+2) 2
  let U := 1000*c*C*powE Q 3
  let den := call PrimeForms.factCode [k] * powE N (2*k) * powE (call PrimeForms.factCode [N]) c
  let side := fun negative => call (numerator negative) [v "d",v "H",v "u",v "v",c,k,N]
  let mag := (side false - side true)+(side true - side false)
  N*powE P k*mag - den*(N*powE Q k*U + 9*(d+1)*powE P k)

def statement (family : Family) (mode : Schedule) : Fm PTm 0 := family.close8 (matrix mode)

def fact : Nat → Nat
  | 0 => 1
  | n+1 => fact n * (n+1)

private theorem factValue (n : Nat) : value PrimeForms.factCode (fun _ => n) = fact n := by
  unfold PrimeForms.factCode
  rw [value_program]
  change overRange 1 _ _ = fact n
  simp only [Discrete.plus]
  change overRange 1 (fun i a => a * (i+1)) n = fact n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun x => x*(n+1)) ih

def logSum (n h : Nat) : Nat :=
  overRange 0 (fun i a => a + h*h/(h+i+1)) (h*(n-1))

theorem logNumerator_reading (n h : Nat) :
    value logNumerator (Fin.cases n (fun _ => h)) = logSum n h := by
  unfold logNumerator
  rw [value_program]
  change overRange 0 _ _ = _
  simp only [Discrete.times,Discrete.minus,Discrete.plus,denote_divE]
  rfl

private def seven (p : Data) (c k N : Nat) : Fin 7 → Nat :=
  Fin.cases p.degreeOffset (Fin.cases p.height (Fin.cases p.pos (Fin.cases p.neg
    (Fin.cases c (Fin.cases k (fun _ => N))))))

def sumSide (p : Data) (negative : Bool) (c k N : Nat) : Nat :=
  overRange 0 (fun i a =>
    let jump := if negative then 2 * (p.logP ((i+1)/2) - p.logP (i/2))
                else p.logP (i+1) - p.logP i
    a + jump * logSum (i+1) N ^ k * ((fact N) / (i+1)) ^ c) N

private theorem callFact {ctx} (x : E ctx) (e) :
    denote (call PrimeForms.factCode [x]) e = fact (denote x e) := by
  change value PrimeForms.factCode _ = _
  convert factValue (denote x e) using 2
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem callLogNum {ctx} (x h : E ctx) (e) :
    denote (call logNumerator [x,h]) e = logSum (denote x e) (denote h e) := by
  change value logNumerator _ = _
  convert logNumerator_reading (denote x e) (denote h e) using 2
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun u => Fin.elim0 u) j) i

theorem numerator_reading (p : Data) (negative : Bool) (c k N : Nat) :
    value (numerator negative) (seven p c k N) = sumSide p negative c k N := by
  cases negative <;> unfold numerator <;> rw [value_program] <;>
    change overRange 0 _ _ = _ <;>
    simp only [Bool.false_eq_true, if_false, if_true, Discrete.times, Discrete.minus, Discrete.plus, Discrete.power,
      Discrete.apply5, callLogNum, denote_divE, callFact] <;> rfl

private theorem envSeven (e : Fin 7 → Nat) :
    e = seven ⟨e 0,e 1,e 2,e 3⟩ (e 4) (e 5) (e 6) := by
  funext ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n+7 => omega

private theorem callSide {ctx} (neg : Bool) (d H u v c k N : E ctx) (e) :
    denote (call (numerator neg) [d,H,u,v,c,k,N]) e =
      sumSide ⟨denote d e,denote H e,denote u e,denote v e⟩ neg
        (denote c e) (denote k e) (denote N e) := by
  change value (numerator neg) _ = _
  exact (congrArg (value (numerator neg)) (envSeven _)).trans (numerator_reading _ neg _ _ _)

/-- Exact native integer inequality, with c and j supplied as actual indices. -/
def check (p : Data) (c j k N : Nat) : Prop :=
  let d := p.degreeOffset+1
  let P := (2*c-1)*j-1
  let Q := 2*j
  let C := 1000*(d+1)^4*(p.height+2)^2
  let U := 1000*c*C*Q^3
  let den := fact k * N^(2*k) * (fact N)^c
  let A := sumSide p false c k N
  let B := sumSide p true c k N
  N*P^k*((A-B)+(B-A)) ≤ den*(N*Q^k*U + 9*(d+1)*P^k)

def Schedule.atCentre : Schedule → Nat → Nat
  | .allDisks, i | .diagonal, i => i+5
  | .lacunary, i => 2^i+4

def Schedule.atIndex : Schedule → Nat → Nat → Nat
  | .allDisks, _, j => j+1
  | .diagonal, c, _ | .lacunary, c, _ => c

theorem matrix_reading (mode : Schedule) (p : Data) (i j k t : Nat) :
    value (matrix mode) (p.work i j k t) = 0 ↔
    check p (mode.atCentre i) (mode.atIndex (mode.atCentre i) j) k (t+1) := by
  cases mode <;> unfold matrix <;> rw [value_program] <;>
    simp only [centre,index,Discrete.minus,Discrete.plus,Discrete.times,
      Discrete.power,callFact,callSide,Nat.sub_eq_zero_iff_le] <;> rfl

theorem statement_reading (family : Family) (mode : Schedule) :
    naturalTerms.Holds (statement family mode) Fin.elim0 ↔
    family.allData (fun p => ∀ i j k t, check p (mode.atCentre i)
      (mode.atIndex (mode.atCentre i) j) k (t+1)) := by
  apply (holds8 family _).trans
  apply family.lift_iff
  intro p
  simp only [matrix_reading]


private theorem familyMono (f : Family) {P Q : Data → Prop} (H : ∀ p, P p → Q p) :
    f.allData P → f.allData Q := by
  cases f <;> simp only [Family.allData]
  · exact H _
  · exact fun h d => H _ (h d)
  · exact fun h d hgt u v => H _ (h d hgt u v)

theorem full_to_diagonal (f : Family) :
    naturalTerms.Holds (statement f .allDisks) Fin.elim0 →
    naturalTerms.Holds (statement f .diagonal) Fin.elim0 := by
  rw [statement_reading, statement_reading]
  apply familyMono
  intro p h i _j k t
  exact h i (i+4) k t

theorem diagonal_to_lacunary (f : Family) :
    naturalTerms.Holds (statement f .diagonal) Fin.elim0 →
    naturalTerms.Holds (statement f .lacunary) Fin.elim0 := by
  rw [statement_reading, statement_reading]
  apply familyMono
  intro p h i _j k t
  have hp : 0 < 2^i := Nat.two_pow_pos i
  have he : 2^i-1+5 = 2^i+4 := by omega
  simpa only [Schedule.atCentre, Schedule.atIndex, he] using h (2^i-1) 0 k t

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.Taylor
