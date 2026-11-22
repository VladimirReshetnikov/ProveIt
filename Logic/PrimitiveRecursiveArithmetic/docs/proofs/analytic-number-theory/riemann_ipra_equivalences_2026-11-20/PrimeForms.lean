import Hypotheses
import SmokePR

/-! Dilation and repeated summation of the prime discrepancy.
All closed sentences below use the original ProveIt first-order syntax. -/
namespace PrimeForms
open LeanProofs.ConciseIPRA PacketLanguage
open RHHierarchy

/-- Count the residues at which the positive and negative parts agree modulo p. -/
def rootsMod : PR 5 := program ["d","H","u","v","p"] <|
  sumTo "z" (v "p") <| eqB
    (modE (powE (v "z") (v "d") + sumTo "i" (v "d")
      (digitE (v "u") (v "H"+2) (v "i") * powE (v "z") (v "i"))) (v "p"))
    (modE (sumTo "i" (v "d")
      (digitE (v "v") (v "H"+2) (v "i") * powE (v "z") (v "i"))) (v "p"))

/-- Integer logarithm of the product over rational primes of p^(number of roots). -/
def primeLog : PR 5 := program ["d","H","u","v","x"] <|
  call logCode [prodTo "p" (v "x"+1) (iteE (call primeCode [v "p"])
    (powE (v "p") (call rootsMod [v "d",v "H",v "u",v "v",v "p"])) 1)]

/-- GCD for positive first argument m (the other branch is its totalization). -/
def gcdCode : PR 2 := program ["m","b"] <|
  iteE (v "m") (maxTo "i" (v "m") ((v "i"+1) *
    eqB (modE (v "m") (v "i"+1)) 0 * eqB (modE (v "b") (v "i"+1)) 0)) (v "b")

def phiCode : PR 1 := program ["m"] <|
  sumTo "i" (v "m") (eqB (call gcdCode [v "m",v "i"]) 1)

/-- Sum φ(e) over e|m with q ≡ 1 mod e, q = p^k. -/
def progressionWeight : PR 2 := program ["m","b"] <|
  sumTo "i" (v "m") (eqB (modE (v "m") (v "i"+1)) 0 *
    eqB (modE (v "b") (v "i"+1)) 0 * call phiCode [v "i"+1])

/-- In the cyclotomic family the exponents are gcd(d,p^k−1), or their
divisor-sum equivalents. The second argument chooses either numerical code. -/
def cyclotomicLog (weight : PR 2) (onlyPrimes : Bool) : PR 5 :=
  if onlyPrimes then
    program ["d","H","u","v","x"] <| call logCode [
      prodTo "p" (v "x"+1) (iteE (call primeCode [v "p"])
        (powE (v "p") (call weight [v "d",v "p"-1])) 1)]
  else
    program ["d","H","u","v","x"] <| call logCode [
      prodTo "p" (v "x"+1) (iteE (call primeCode [v "p"])
        (prodTo "j" (call logCode [v "x"]) <| iteE
          (leB (powE (v "p") (v "j"+1)) (v "x"))
          (powE (v "p") (call weight [v "d",powE (v "p") (v "j"+1)-1])) 1) 1)]

def factCode : PR 1 := program ["n"] <| prodTo "i" (v "n") (v "i"+1)

def chooseCode : PR 2 := program ["n","k"] <|
  iteE (leB (v "k") (v "n"))
    (divE (call factCode [v "n"]) (call factCode [v "k"] * call factCode [v "n"-v "k"])) 0

/-- t=N−100. For j>0 the coefficient of the sample t' is
choose(t−t'+j−1,j−1), for 0≤t'≤t. We accumulate the positive and
negative summands separately until the final absolute difference. -/
def aggregate (data : PR 5) : PR 7 := program ["d","H","u","v","t","a","j"] <|
  let right := iteE (v "j")
    (sumTo "i" (v "t"+1) <|
      call chooseCode [v "t"-v "i"+(v "j"-1),v "j"-1] *
      call data [v "d",v "H",v "u",v "v",v "a"*(v "i"+100)])
    (call data [v "d",v "H",v "u",v "v",v "a"*(v "t"+100)])
  let left := v "a" * iteE (v "j")
    (sumTo "i" (v "t"+1) <|
      call chooseCode [v "t"-v "i"+(v "j"-1),v "j"-1] *
      call data [v "d",v "H",v "u",v "v",v "i"+100])
    (call data [v "d",v "H",v "u",v "v",v "t"+100])
  (right-left)+(left-right)

/-- K is the entire free coefficient, including any dilation factor. -/
def matrix (data : PR 5) : PR 8 := program ["d0","H","u","v","t","a","j","K"] <|
  let n := v "t"+100
  let bound := v "K" * powE n (v "j") * powE (1+call logCode [v "a"*n]) 2
  powE (call (aggregate data) [v "d0"+1,v "H",v "u",v "v",v "t",v "a",v "j"]) 2 -
    n * powE bound 2

def fixed (data : PR 5) (offset order : Nat) : PR 5 := program ["d0","H","u","v","t"] <|
  let a : E ["d0","H","u","v","t"] := .num (offset+2)
  let k := 1000*a * powE (v "d0"+2) 4 * powE (v "H"+2) 2
  call (matrix data) [v "d0",v "H",v "u",v "v",v "t",a,.num order,k]

def boundMatrix (data : PR 5) : PR 7 := program ["d0","H","u","v","t","b","j"] <|
  let a := v "b"+2
  let k := 1000*a * powE (v "d0"+2) 4 * powE (v "H"+2) 2
  call (matrix data) [v "d0",v "H",v "u",v "v",v "t",a,v "j",k]

inductive Family | riemann | dirichlet | dedekind

/-- Lifts a relation on the four polynomial parameters to its intended family. -/
def select (family : Family)
    (pred : {n : Nat} → PTm n → PTm n → PTm n → PTm n → Fm PTm n) : Fm PTm 0 :=
  match family with
  | .riemann => pred PTm.zero PTm.zero PTm.zero (PTm.succ PTm.zero)
  | .dirichlet => .all (pred (.var 0) PTm.zero PTm.zero (PTm.succ PTm.zero))
  | .dedekind => .all (.all (.all (.all (pred (.var 3) (.var 2) (.var 1) (.var 0)))))

def packet (family : Family) (data : PR 5) (offset order : Nat) : Fm PTm 0 :=
  match family with
  | .riemann => RHOf (fixed data offset order)
  | .dirichlet => GRHOf (fixed data offset order)
  | .dedekind => ERHOf (fixed data offset order)

private def termApp {n k : Nat} (f : PR k) (args : List (PTm n)) (h : args.length = k := by rfl) : PTm n :=
  .app f (fun i => args[i.val]'(h ▸ i.isLt))

/-- ∀F ∀b,j,t for the prescribed envelope, a=b+2. -/
def allPackets (family : Family) (data : PR 5) : Fm PTm 0 := select family fun d H u v =>
  .all (.all (.all (.eq (termApp (boundMatrix data) [
    Syn.shift (Syn.shift (Syn.shift d)), Syn.shift (Syn.shift (Syn.shift H)),
    Syn.shift (Syn.shift (Syn.shift u)), Syn.shift (Syn.shift (Syn.shift v)), .var 0, .var 2, .var 1])
    PTm.zero)))

/-- ∀F ∃K ∀t for the specified dilation and order. -/
def witness (family : Family) (data : PR 5) (offset order : Nat) : Fm PTm 0 :=
  select family fun d H u v => .ex (.all (.eq (termApp (matrix data) [
      Syn.shift (Syn.shift d), Syn.shift (Syn.shift H), Syn.shift (Syn.shift u), Syn.shift (Syn.shift v), .var 0,
      .app (numeral (offset+2)) Fin.elim0, .app (numeral order) Fin.elim0, .var 1]) PTm.zero))

/-- The hierarchy implications for every common data source and parameter pair. -/
theorem dedekind_to_dirichlet (data : PR 5) (b j : Nat) :
    Prf PRAAx [] (.imp (packet .dedekind data b j) (packet .dirichlet data b j)) :=
  RHHierarchy.erh_implies_grh _

theorem dirichlet_to_riemann (data : PR 5) (b j : Nat) :
    Prf PRAAx [] (.imp (packet .dirichlet data b j) (packet .riemann data b j)) :=
  RHHierarchy.grh_implies_rh _

/-- Natural-number indexed summation, dropping t=0 (all sequences of interest
are zero below 100). The following bound is independent of the source. -/
def prefixes (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => prefixes f n + f (n+1)

def repeated (j : Nat) (f : Nat → Int) : Nat → Int :=
  match j with
  | 0 => f
  | k+1 => prefixes (repeated k f)

theorem prefix_bound {f : Nat → Int} (n M : Nat) (h : ∀ m, m ≤ n → (f m).natAbs ≤ M) :
    (prefixes f n).natAbs ≤ n*M := by
  induction n with
  | zero => simp [prefixes]
  | succ n ih =>
    calc
      _ ≤ (prefixes f n).natAbs + (f (n+1)).natAbs := Int.natAbs_add_le ..
      _ ≤ n*M+M := Nat.add_le_add (ih (fun m hm => h m (by omega))) (h _ (by omega))
      _ = _ := (Nat.succ_mul _ _).symm

theorem repeated_bound (j : Nat) (f : Nat → Int) (n M : Nat)
    (h : ∀ m, m ≤ n → (f m).natAbs ≤ M) : (repeated j f n).natAbs ≤ n^j*M := by
  induction j generalizing n with
  | zero => simpa [repeated] using h n (by omega)
  | succ j ih =>
    calc
      _ ≤ n*(n^j*M) := prefix_bound n _ (fun m hm =>
        (ih m (fun i hi => h i (by omega))).trans
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm _)))
      _ = _ := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

theorem square_budget {n x y A B : Nat}
    (hx : x^2 ≤ n*A^2) (hy : y^2 ≤ n*B^2) : (x+y)^2 ≤ n*(A+B)^2 := by
  have cross : x*y ≤ n*(A*B) := by
    apply Nat.mul_self_le_mul_self_iff.mp
    simpa only [Nat.pow_two, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
      using Nat.mul_le_mul hx hy
  have sum := Nat.add_le_add (Nat.add_le_add hx cross) (Nat.add_le_add cross hy)
  simpa only [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_left_comm, Nat.mul_comm,
    Nat.mul_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using sum

def envelope (f : Nat → Int) (scale : Nat → Nat) (K : Nat) : Prop :=
  ∀ n, (f n).natAbs^2 ≤ n*(K*scale n)^2

/-- Translate a supplied arithmetic growth constant across an additive
perturbation with certified constant C, keeping the squared envelope exact. -/
theorem transfer_envelope {f g : Nat → Int} {scale : Nat → Nat} {K C : Nat}
    (bound : envelope f scale K) (delta : envelope (fun n => g n - f n) scale C) :
    envelope g scale (K+C) := by
  intro n
  have tri : (g n).natAbs ≤ (f n).natAbs + (g n-f n).natAbs := by
    have add := Int.natAbs_add_le (f n) (g n-f n)
    have cancel : f n + (g n-f n) = g n := by omega
    rwa [cancel] at add
  calc
    _ ≤ ((f n).natAbs+(g n-f n).natAbs)^2 := Nat.pow_le_pow_left tri _
    _ ≤ n*((K+C)*scale n)^2 := by
      rw [Nat.add_mul]
      exact square_budget (bound n) (delta n)

theorem prefix_sub (f g : Nat → Int) (n : Nat) :
    prefixes (fun m => f m - g m) n = prefixes f n - prefixes g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixes, ih]
    omega

theorem repeated_sub (j : Nat) (f g : Nat → Int) :
    repeated j (fun m => f m-g m) = fun m => repeated j f m - repeated j g m := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    change prefixes (repeated j (fun m => f m-g m)) n = _
    rw [ih]
    exact prefix_sub _ _ _

open RiemannIPRA.Smoke in
#guard vecEval rootsMod #v[2,0,1,0,3] == 0

open RiemannIPRA.Smoke in
#guard vecEval rootsMod #v[2,0,1,0,5] == 2

open RiemannIPRA.Smoke in
#guard vecEval gcdCode #v[6,8] == vecEval progressionWeight #v[6,8]

open RiemannIPRA.Smoke in
#guard vecEval chooseCode #v[3,1] == 3

end PrimeForms
