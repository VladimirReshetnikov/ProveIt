import IPRADerivations.Core.IntCertificates

/-!
# Orbit–stabilizer and the orbit-counting lemma

Packet: `combinatorics/Combinatorics-iPRA`, `actions.tex`, result 63 ("Orbit–stabilizer and the orbit-counting
lemma"): "For every `x ∈ X`, `|Gx| |G_x| = s`, `s |X/G| = ∑_{g ∈ G} |X^g|`." The group has `s` elements indexed by
`Fin s`, and the counting data are tables of integer terms (bits in an action). As iPRA derivations:

* `orbit_stabilizer`: with `T g y` the table of `g x = y` (each `g` sends `x` to exactly one point), `o y` the
  indicator of the orbit of `x`, and every fibre over an orbit point of the size `st` of the stabilizer ("The map
  `h ↦ t_y h` from `G_x` onto the elements sending `x` to `y` has inverse `g ↦ t_y⁻¹ g`. Summing these fiber
  sizes gives the first formula"): `s = (∑_y o_y) · st`;
* `orbit_count`: with `F g x` the table of `g x = x`, `O x c` the membership of `x` in the orbit `c` (each point in
  exactly one of the `m` orbits), and `∑_{x ∈ c} |G_x| = s` for every orbit: "Count pairs `(g, x)` with `g x = x`.
  Each orbit contributes `|Gx| |G_x| = s`, while a fixed `g` contributes `|X^g|`", so `∑_g |X^g| = m s`.

Not derived: the group axioms behind the fibre bijections, and Pólya's inventory formula (result 64).
-/

namespace LeanProofs.IPRA.Combinatorics.OrbitCounting

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n s X m : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

theorem orbit_stabilizer_sum (T : Fin s → Fin X → R) (o : Fin X → R) (st : R)
    (hrow : ∀ g, ∑ y, T g y = 1) (hfib : ∀ y, ∑ g, T g y = o y * st) : (s : R) = (∑ y, o y) * st := by
  have h1 : ∑ g, ∑ y, T g y = (s : R) := by
    rw [Finset.sum_congr rfl fun g _ => hrow g, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, _root_.mul_one]
  have h2 : ∑ g, ∑ y, T g y = (∑ y, o y) * st := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => hfib y, ← Finset.sum_mul]
  rw [← h1, h2]

theorem orbit_count_sum (F : Fin s → Fin X → R) (O : Fin X → Fin m → R) (S : R)
    (hO : ∀ x, ∑ c, O x c = 1) (hc : ∀ c, ∑ x, O x c * ∑ g, F g x = S) :
    ∑ g, ∑ x, F g x = (m : R) * S := by
  have e : ∀ x, ∑ g, F g x = ∑ c, O x c * ∑ g, F g x := fun x => by
    rw [← Finset.sum_mul, hO x, _root_.one_mul]
  have h1 : ∑ g, ∑ x, F g x = ∑ x, ∑ c, O x c * ∑ g, F g x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => e x
  rw [h1, Finset.sum_comm, Finset.sum_congr rfl fun c _ => hc c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end Ring

/-! ## The derivations -/

/-- Orbit–stabilizer: `s = |Gx| · |G_x|`. -/
theorem orbit_stabilizer (T : Fin s → Fin X → ZT n) (o : Fin X → ZT n) (st : ZT n)
    (hrow : ∀ g, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun y => T g y) (ZT.natLit 1))
    (hfib : ∀ y, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun g => T g y) (o y * st)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit s) (ZT.sumFin o * st) := by
  have hrow1 : ∀ g, ∑ y, ZT.toZ Γ (T g y) = 1 := fun g => by
    have h := ZT.toZ_eq (hrow g)
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using h
  have hfib1 : ∀ y, ∑ g, ZT.toZ Γ (T g y) = ZT.toZ Γ (o y) * ZT.toZ Γ st := fun y => by
    have h := ZT.toZ_eq (hfib y)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using h
  have e := orbit_stabilizer_sum (fun g y => ZT.toZ Γ (T g y)) (fun y => ZT.toZ Γ (o y)) _ hrow1 hfib1
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The orbit-counting lemma: `∑_g |X^g| = m s` for `m` orbits. -/
theorem orbit_count (F : Fin s → Fin X → ZT n) (O : Fin X → Fin m → ZT n) (S : ZT n)
    (hO : ∀ x, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun c => O x c) (ZT.natLit 1))
    (hc : ∀ c, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun x => O x c * ZT.sumFin fun g => F g x) S) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun g => ZT.sumFin fun x => F g x) (ZT.natLit m * S) := by
  have hO1 : ∀ x, ∑ c, ZT.toZ Γ (O x c) = 1 := fun x => by
    have h := ZT.toZ_eq (hO x)
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using h
  have hc1 : ∀ c, ∑ x, ZT.toZ Γ (O x c) * ∑ g, ZT.toZ Γ (F g x) = ZT.toZ Γ S := fun c => by
    have h := ZT.toZ_eq (hc c)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using h
  have e := orbit_count_sum (fun g x => ZT.toZ Γ (F g x)) (fun x c => ZT.toZ Γ (O x c)) _ hO1 hc1
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

end LeanProofs.IPRA.Combinatorics.OrbitCounting
