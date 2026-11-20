import Std
import Init.Data.Rat.Lemmas

/-!
# Finite algebraic topology: checked interfaces and structural lemmas

This standalone file uses Lean's ambient dependent type theory.  It is NOT an
object-language proof in iPRA.  Finite function types below are intended to be
replaced by natural-number-coded tables in that final translation.

Definitions ending in `Target` state uncompleted proof obligations.  No axiom,
`sorry`, or `admit` is used.  Rank computation, Euler-Poincare for arbitrary
matrices, and the complete finite-sheaf checker remain blueprint obligations.
-/

namespace GeneralTopologyIPRA.Algebraic

abbrev Vec (n : Nat) := Fin n → Rat
abbrev VecInt (n : Nat) := Fin n → Int
abbrev Matrix (m n : Nat) := Fin m → Fin n → Rat

def qsum (n : Nat) (f : Fin n → Rat) : Rat :=
  (List.ofFn f).foldl (fun a b => a + b) 0

def mul {l m n : Nat} (a : Matrix l m) (b : Matrix m n) : Matrix l n :=
  fun i j => qsum m (fun k => a i k * b k j)

def app {m n : Nat} (a : Matrix m n) (v : Vec n) : Vec m :=
  fun i => qsum n (fun j => a i j * v j)

def ident (n : Nat) : Matrix n n :=
  fun i j => if i = j then 1 else 0

def rankDiag (m n r : Nat) : Matrix m n :=
  fun i j => if i.val = j.val ∧ i.val < r then 1 else 0

def MatrixEq {m n : Nat} (a b : Matrix m n) : Prop :=
  ∀ i j, a i j = b i j

def IsZero {n : Nat} (v : Vec n) : Prop := ∀ i, v i = 0

def zeroVecInt (n : Nat) : VecInt n := fun _ => 0

/-- A fully explicit two-sided reduction to a rank diagonal matrix. -/
structure RankCertificate {m n : Nat} (a : Matrix m n) where
  rank : Nat
  leRows : rank ≤ m
  leCols : rank ≤ n
  left : Matrix m m
  leftInv : Matrix m m
  right : Matrix n n
  rightInv : Matrix n n
  leftInvLeft : MatrixEq (mul leftInv left) (ident m)
  leftLeftInv : MatrixEq (mul left leftInv) (ident m)
  rightInvRight : MatrixEq (mul rightInv right) (ident n)
  rightRightInv : MatrixEq (mul right rightInv) (ident n)
  reduces : MatrixEq (mul (mul left a) right) (rankDiag m n rank)

/-- Obligation A02: constructive matrix reduction, with a coded PR algorithm. -/
def MatrixReductionTarget : Prop :=
  ∀ m n (a : Matrix m n), Nonempty (RankCertificate a)

structure ChainComplex where
  top : Nat
  dim : Nat → Nat
  bounded : ∀ k, top < k → dim k = 0
  boundary : (k : Nat) → Matrix (dim k) (dim (k + 1))
  boundarySquared : ∀ k i j,
    mul (boundary k) (boundary (k + 1)) i j = 0

def ChainMap (c d : ChainComplex) (f : (k : Nat) → Matrix (d.dim k) (c.dim k)) :
    Prop :=
  ∀ k, MatrixEq (mul (d.boundary k) (f (k + 1)))
                   (mul (f k) (c.boundary k))

/-- The individual integral-chain homotopy equation in a fixed degree. -/
def HomotopyAt {a b c d : Nat}
    (f g : VecInt a → VecInt c) (dC : VecInt a → VecInt b)
    (dD : VecInt d → VecInt c) (h : VecInt a → VecInt d)
    (previous : VecInt b → VecInt c) : Prop :=
  ∀ z i, f z i - g z i = dD (h z) i + previous (dC z) i

/-- Checked structural core of A04: homologous maps differ by a boundary on cycles. -/
theorem homotopy_on_cycle {a b c d : Nat}
    (f g : VecInt a → VecInt c) (dC : VecInt a → VecInt b)
    (dD : VecInt d → VecInt c) (h : VecInt a → VecInt d)
    (previous : VecInt b → VecInt c)
    (H : HomotopyAt f g dC dD h previous)
    (previous_zero : ∀ i, previous (zeroVecInt b) i = 0)
    (z : VecInt a) (hz : dC z = zeroVecInt b) :
    ∃ w : VecInt d, ∀ i, f z i - g z i = dD w i := by
  refine ⟨h z, ?_⟩
  intro i
  have hi := H z i
  rw [hz, previous_zero i] at hi
  exact hi.trans (Int.add_zero _)

/-- Integer-valued alternating lists give the local Euler telescoping step. -/
def alternating : List Int → Int
  | [] => 0
  | a :: xs => a - alternating xs

theorem alternating_cons (a : Int) (xs : List Int) :
    alternating (a :: xs) = a - alternating xs := rfl

/-- Checked arithmetic cancellation used when neighboring ranks are paired. -/
theorem euler_local_cancellation (b r s tail : Int) :
    (b + r + s) - (s + tail) = b + r - tail := by
  omega

def alternatingFrom : Nat → (Nat → Int) → Nat → Int
  | 0, _, _ => 0
  | n + 1, f, k => f k - alternatingFrom n f (k + 1)

def endpointSign : Nat → Int
  | 0 => 1
  | n + 1 => -endpointSign n

theorem euler_telescope (n : Nat) (b r : Nat → Int) (k : Nat) :
    alternatingFrom n (fun i => b i + r i + r (i + 1)) k =
      alternatingFrom n b k + r k - endpointSign n * r (k + n) := by
  induction n generalizing k with
  | zero => simp [alternatingFrom, endpointSign]
  | succ n ih =>
    simp only [alternatingFrom, endpointSign]
    rw [ih (k + 1)]
    have hidx : k + 1 + n = k + (n + 1) := by omega
    rw [hidx, Int.neg_mul]
    omega

/-- Checked Euler telescoping, with rank-nullity decomposition supplied. -/
theorem euler_from_rank_data (n : Nat) (c b r : Nat → Int)
    (decomposition : ∀ k, c k = b k + r k + r (k + 1))
    (left_endpoint : r 0 = 0) (right_endpoint : r n = 0) :
    alternatingFrom n c 0 = alternatingFrom n b 0 := by
  have functions_equal : c = (fun k => b k + r k + r (k + 1)) :=
    funext decomposition
  rw [functions_equal, euler_telescope]
  simp [left_endpoint, right_endpoint]

def paritySign (k : Nat) : Int := if k % 2 = 0 then 1 else -1

def euler (n : Nat) (c : Fin n → Nat) : Int :=
  (List.ofFn (fun k => paritySign k.val * Int.ofNat (c k))).foldl (· + ·) 0

/--
Endpoint of the full finite telescoping proof.  The premises explicitly state
the rank-nullity data; deriving them is A02, not an implicit imported theorem.
-/
def EulerPoincareTarget : Prop :=
  ∀ n (c b : Fin n → Nat) (r : Nat → Nat),
    r 0 = 0 → r n = 0 →
    (∀ k : Fin n, c k = b k + r k.val + r (k.val + 1)) →
    euler n c = euler n b

/-! The function-sheaf gluing kernel uses supplied finite cover selectors. -/

structure CoverData (n ell : Nat) where
  carrier : Fin n → Bool
  member : Fin ell → Fin n → Bool
  contained : ∀ i x, member i x = true → carrier x = true
  choose : (x : Fin n) → carrier x = true → Fin ell
  choose_mem : ∀ x hx, member (choose x hx) x = true

def LocalFunctions {n ell : Nat} (c : CoverData n ell) (a : Nat) :=
  (i : Fin ell) → (x : Fin n) → c.member i x = true → Fin a

def GlobalFunction {n ell : Nat} (c : CoverData n ell) (a : Nat) :=
  (x : Fin n) → c.carrier x = true → Fin a

def Matching {n ell a : Nat} (c : CoverData n ell)
    (s : LocalFunctions c a) : Prop :=
  ∀ i j x (hi : c.member i x = true) (hj : c.member j x = true),
    s i x hi = s j x hj

def glueFunctions {n ell a : Nat} (c : CoverData n ell)
    (s : LocalFunctions c a) : GlobalFunction c a :=
  fun x hx => s (c.choose x hx) x (c.choose_mem x hx)

theorem glue_restricts {n ell a : Nat} (c : CoverData n ell)
    (s : LocalFunctions c a) (hs : Matching c s) :
    ∀ i x (hi : c.member i x = true),
      glueFunctions c s x (c.contained i x hi) = s i x hi := by
  intro i x hix
  exact hs (c.choose x (c.contained i x hix)) i x
    (c.choose_mem x (c.contained i x hix)) hix

theorem glue_unique {n ell a : Nat} (c : CoverData n ell)
    (s : LocalFunctions c a) (t : GlobalFunction c a)
    (ht : ∀ i x (hi : c.member i x = true),
      t x (c.contained i x hi) = s i x hi) :
    ∀ x (hx : c.carrier x = true), t x hx = glueFunctions c s x hx := by
  intro x hx
  exact ht (c.choose x hx) x (c.choose_mem x hx)

/-!
Sections and selectors depend on proofs of domain membership.  They therefore
handle empty opens and empty codomains without adding arbitrary values outside
the domain.  An empty cover of an empty open has its unique empty section; no
index in an empty covering family is selected.
-/

/-- A finite presheaf interface with the open-set list supplied explicitly. -/
structure FinitePresheaf (o : Nat) where
  le : Fin o → Fin o → Bool
  size : Fin o → Nat
  restriction : (u v : Fin o) → le v u = true → Fin (size u) → Fin (size v)
  leRefl : ∀ u, le u u = true
  leTrans : ∀ u v w, le w v = true → le v u = true → le w u = true
  restrictionId : ∀ u s, restriction u u (leRefl u) s = s
  restrictionComp : ∀ u v w (hvu : le v u = true) (hwv : le w v = true) s,
    restriction v w hwv (restriction u v hvu s) =
      restriction u w (leTrans u v w hwv hvu) s

/-!
Further blueprint obligations:

1. Bit-mask topology, minimal neighborhoods N_x, and finite cover enumerator.
2. Canonical-cover gluing checker with explicit bounds 2^n * (M+1)^(n+1).
3. Soundness/completeness of that checker (A11), then A13--A16.
4. Primitive recursive coding proofs for rational matrix and table algorithms.

The human chapter gives all definitions and the constructive proofs.  No
uncompleted obligation is exposed here as a theorem or as a global axiom.
-/


end GeneralTopologyIPRA.Algebraic

-- Complete theorem axiom audit for this standalone file.
#print axioms GeneralTopologyIPRA.Algebraic.homotopy_on_cycle
#print axioms GeneralTopologyIPRA.Algebraic.alternating_cons
#print axioms GeneralTopologyIPRA.Algebraic.euler_local_cancellation
#print axioms GeneralTopologyIPRA.Algebraic.euler_telescope
#print axioms GeneralTopologyIPRA.Algebraic.euler_from_rank_data
#print axioms GeneralTopologyIPRA.Algebraic.glue_restricts
#print axioms GeneralTopologyIPRA.Algebraic.glue_unique
