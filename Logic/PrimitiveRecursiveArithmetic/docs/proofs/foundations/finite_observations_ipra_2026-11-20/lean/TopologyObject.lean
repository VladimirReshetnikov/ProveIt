import IPRADerivations.Core.Integers

/-! Coded polynomial forward differences in the ordinary iPRA proof system.
The coefficient list fixes the syntax tree externally. Its entries are arbitrary
integer terms, so all starting values, coefficients and steps may be parameters. -/
namespace CrossingObject

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm Prf

def Δ {R : Type*} [Sub R] (f : Nat → R) : Nat → Nat → R
  | 0, j => f j
  | n+1, j => Δ f n (j+1) - Δ f n j

def poly {R : Type*} [Add R] [Mul R] (a : R) : List R → R → R
  | [], _ => a
  | c::tail, x => c+x*poly a tail x

def grid {R : Type*} [Add R] (x h : R) : Nat → R
  | 0 => x
  | j+1 => grid x h j+h

def factor {R : Type*} [Mul R] (lit : Nat → R) (h : R) : Nat → R
  | 0 => lit 1
  | d+1 => lit (d+1)*h*factor lit h d

section Algebra
variable {R : Type*} [CommRing R]

private theorem linear_prod (f l : Nat → R) (h : R)
    (hl : ∀ k, l (k+1) = l k + h) (n k : Nat) :
    Δ (fun i => l i*f i) (n+1) k =
      l (k+(n+1)) * Δ f (n+1) k + ((n+1 : Nat) : R)*h*Δ f n k := by
  induction n generalizing k with
  | zero =>
    simp [Δ, hl k]
    ring
  | succ n ih =>
    change Δ _ (n+1) (k+1) - Δ _ (n+1) k =
      l (k+(n+1+1)) * (Δ f (n+1) (k+1) - Δ f (n+1) k) +
      ((n+1+1 : Nat) : R)*h*Δ f (n+1) k
    rw [ih (k+1), ih k]
    have hk : k+1+(n+1) = k+(n+1+1) := by omega
    rw [hk, show k+(n+1+1) = k+(n+1)+1 by omega, hl, Nat.cast_succ (n+1)]
    rw [show Δ f (n+1) k = Δ f n (k+1) - Δ f n k from rfl]
    ring

private theorem add_const (f : Nat → R) (c : R) (d k : Nat) :
    Δ (fun i => c+f i) (d+1) k = Δ f (d+1) k := by
  induction d generalizing k with
  | zero => simp [Δ]
  | succ d ih =>
    change Δ _ (d+1) (k+1) - Δ _ (d+1) k = _
    rw [ih, ih]
    rfl

private theorem polynomial_difference (x h a : R) (coeff : List R) (k : Nat) :
    Δ (fun i => poly a coeff (grid x h i)) coeff.length k =
      factor (fun j => (j : R)) h coeff.length * a := by
  let l := grid x h
  have hl (j : Nat) : l (j+1) = l j+h := rfl
  induction coeff generalizing k with
  | nil => simp [Δ, poly, factor]
  | cons c tail ih =>
    let f := fun i => poly a tail (l i)
    change Δ (fun i => c+l i*f i) (tail.length+1) k =
      factor _ h (tail.length+1) * a
    rw [add_const, linear_prod f l h hl]
    have hk : Δ f tail.length k = factor (fun j => (j : R)) h tail.length*a := ih k
    have hn : Δ f tail.length (k+1) = factor (fun j => (j : R)) h tail.length*a := ih (k+1)
    have hz : Δ f (tail.length+1) k = 0 := by
      change Δ f tail.length (k+1) - Δ f tail.length k = 0
      rw [hk, hn, sub_self]
    rw [hz, hk, factor]
    ring
end Algebra

section Object
variable {n : Nat} (Γ : List (Fm PTm n))

private theorem interp_grid (x h : ZT n) (j : Nat) :
    ZT.toZ Γ (grid x h j) = grid (ZT.toZ Γ x) (ZT.toZ Γ h) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [grid, ZT.toZ_add, ih]

private theorem interp_poly (a x : ZT n) (cs : List (ZT n)) :
    ZT.toZ Γ (poly a cs x) = poly (ZT.toZ Γ a) (cs.map (ZT.toZ Γ)) (ZT.toZ Γ x) := by
  induction cs with
  | nil => rfl
  | cons c t ih => simp only [poly, List.map_cons, ZT.toZ_add, ZT.toZ_mul, ih]

private theorem interp_diff (f : Nat → ZT n) (d j : Nat) :
    ZT.toZ Γ (Δ f d j) = Δ (fun i => ZT.toZ Γ (f i)) d j := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih => simp only [Δ, ZT.toZ_sub, ih]

private theorem interp_factor (h : ZT n) (d : Nat) :
    ZT.toZ Γ (factor ZT.natLit h d) =
      factor (fun j => (j : Groth (Q Γ))) (ZT.toZ Γ h) d := by
  induction d with
  | zero => simp [factor]
  | succ d ih => simp only [factor, ZT.toZ_mul, ZT.toZ_natLit, ih]

/-- For any externally specified coefficient list, the result is an object
derivation from iPRA axioms alone in the supplied (possibly empty) context. -/
theorem top_difference (x h a : ZT n) (cs : List (ZT n)) (j : Nat) :
    Γ ⊢[PRAAx] ZT.eq (Δ (fun i => poly a cs (grid x h i)) cs.length j)
      (factor ZT.natLit h cs.length*a) := by
  apply ZT.derive
  rw [interp_diff, ZT.toZ_mul, interp_factor]
  simp only [interp_poly, interp_grid]
  simpa only [List.length_map] using
    polynomial_difference (ZT.toZ Γ x) (ZT.toZ Γ h) (ZT.toZ Γ a) (cs.map (ZT.toZ Γ)) j
end Object
end CrossingObject

#print axioms CrossingObject.top_difference
