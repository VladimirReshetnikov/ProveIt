import FabiusFunction.QLucas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Cyclic sieving for `k`-subsets of `ZMod n`

Let `C_n` act on the `k`-element subsets of `ℤ/nℤ` by translation and let `ω` be a primitive
`n`-th root of unity.  The source theorem (`thm:csp-subsets`) asserts that the triple
`(k`-subsets, `C_n`, `[n,k]_q)` exhibits the *cyclic sieving phenomenon*: the number of
`k`-subsets fixed by the `j`-th power of the generator equals `[n,k]_q` evaluated at `ω^j`.

## What is covered

* `IsCyclicSieving` — the cyclic sieving predicate, stated exactly as in the source: for a
  permutation `σ` of a type `α`, a finset `s : Finset α`, a ring element `ω : R` and a
  polynomial `F : Polynomial R`,
  `∀ j, (#{x ∈ s | σ^j x = x} : R) = F.eval (ω ^ j)`.
  Mathlib has no cyclic-sieving API, so the predicate is introduced here.
* `card_rotationFix` — the combinatorial half, in the strengthened form described below: for
  **any** `a : ZMod n` of additive order `d`, and any factorisation `n = g * d`,
  `#(rotationFix k a) = if d ∣ k then g.choose (k / d) else 0`.
  This is the one sentence of the source proof ("its orbits all have size `d`, there are `n/d`
  of them, and a subset is fixed exactly when it is a union of orbits") which is asserted
  without proof; it is what almost all of this file establishes.
* `isPrimitiveRoot_pow_addOrderOf` — the source's unproved one-liner "the number `ω^j` is a
  primitive `d`-th root", i.e. `IsPrimitiveRoot (ω ^ j) (addOrderOf (j : ZMod n))`.  Stated for
  an arbitrary `CommMonoid`; no domain and no `NeZero n` are needed.
* `gaussianBinomial_isPrimitiveRoot_mul` — the algebraic half: for `ζ` a primitive `d`-th root
  of unity in a commutative integral domain,
  `[g * d, k]_ζ = if d ∣ k then (g.choose (k / d) : R) else 0`.
  This is `Fabius.gaussianBinomial_q_lucas` specialised to a row that is a multiple of `d`.
* `card_rotationFix_cast` and `isCyclicSieving_powersetCard` — the theorem itself, the latter
  packaged through the `IsCyclicSieving` predicate with the sieving polynomial
  `gaussianBinomial (X : Polynomial R) n k`.

## How the statement here is stronger than the source

* **Coefficient ring.**  The source works in `ℤ[q]` and evaluates in `ℂ`.  Everything below
  holds over an arbitrary commutative integral domain `R` carrying a primitive `n`-th root of
  unity, positive characteristic included; `gaussianBinomial_q_lucas` is already stated at that
  generality, so this costs nothing.
* **No range hypothesis on `k`.**  The source gives none, and none is needed: for `k > n` both
  sides vanish, by `Nat.choose_eq_zero_of_lt` on one side and the zero extension
  `gaussianBinomial_eq_zero_of_lt` on the other.  The degenerate cases `k = 0` (`d ∣ 0` and
  `g.choose 0 = 1 = [n,0]_q`), `j = 0` (`d = 1`, `g = n`, both sides `n.choose k`) and `j ≥ n`
  are likewise covered with no case split.
* **`j` ranges over all of `ℕ`**, not over a residue system.
* **Arbitrary group element.**  `card_rotationFix` is proved for an arbitrary `a : ZMod n`,
  not only for the powers `j • 1` of the distinguished generator, so it is reusable for cyclic
  sieving statements about other translation actions.

`n > 0` is genuinely required: `ZMod 0 = ℤ` is not a `Fintype`.

## What is NOT covered

* No general cyclic sieving theory.  In particular there is no proof that the property is
  independent of the choice of primitive `|C|`-th root `ω` (true by Galois conjugation), no
  polynomial-quotient reformulation `#Fix(c^j) = F(q) mod (q^n - 1)`, and no statement for any
  action other than translation on subsets.
* `thm:q-lucas` is not reproved here.  It is imported from `FabiusFunction.QLucas` in its
  already-evaluated form `gaussianBinomial_q_lucas`, so the source's implicit passage from a
  congruence modulo `Φ_d(q)` to an evaluation at `q = ω^j` is discharged upstream.
* No claim that a `q`-analogue exhibits cyclic sieving in general; only the subset case.

## Method

The combinatorial half avoids quotient types, `AddSubgroup.zmultiples` and gcd arithmetic
entirely.  With `n = g * d` and `d` the additive order of `a`, the ring map
`zmodProj : ZMod n →+* ZMod g` of reduction modulo `g` is a concrete model of the orbit space:
its fibres are exactly the `⟨a⟩`-orbits (`zmodProj_eq_zero_iff`), each of size `d`
(`card_filter_zmodProj`, obtained by *counting*, never by `ZMod.val` arithmetic), and a subset
is translation invariant exactly when it is a union of fibres (`image_add_eq_iff`).  The
`k`-subsets fixed by translation then biject with the `(k/d)`-subsets of `ZMod g`
(`card_rotationFix`), and `Fintype`/`DecidableEq` instances are structural throughout.
-/

set_option autoImplicit false

open scoped BigOperators

open Finset

namespace Fabius

/-! ### Translation of finite subsets -/

section Rotation

variable {n : ℕ}

/-- Translation by `a`, as a permutation of the finite subsets of `ZMod n`. -/
def rotation (a : ZMod n) : Equiv.Perm (Finset (ZMod n)) where
  toFun S := S.image (a + ·)
  invFun S := S.image (-a + ·)
  left_inv S := by
    show (S.image (a + ·)).image (-a + ·) = S
    rw [Finset.image_image]
    have hcomp : ((fun x : ZMod n => -a + x) ∘ fun x : ZMod n => a + x)
        = fun x : ZMod n => x := by
      funext x
      simp
    rw [hcomp, Finset.image_id']
  right_inv S := by
    show (S.image (-a + ·)).image (a + ·) = S
    rw [Finset.image_image]
    have hcomp : ((fun x : ZMod n => a + x) ∘ fun x : ZMod n => -a + x)
        = fun x : ZMod n => x := by
      funext x
      simp
    rw [hcomp, Finset.image_id']

/-- Translation acts on subsets by taking the pointwise image. -/
@[simp] theorem rotation_apply (a : ZMod n) (S : Finset (ZMod n)) :
    rotation a S = S.image (a + ·) := rfl

/-- The `m`-th power of translation by `a` is translation by `m • a`. -/
theorem rotation_pow_apply (a : ZMod n) (m : ℕ) (S : Finset (ZMod n)) :
    (rotation a ^ m) S = rotation (m • a) S := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [rotation_apply]
      rw [Finset.image_image, succ_nsmul]
      have hcomp : ((fun x : ZMod n => m • a + x) ∘ fun x : ZMod n => a + x)
          = fun x : ZMod n => m • a + a + x := by
        funext x
        simp only [Function.comp_apply]
        exact (add_assoc _ _ _).symm
      rw [hcomp]

/-- A translation-invariant subset is closed under all natural multiples of the translation. -/
theorem nsmul_add_mem_of_image_add_eq {a : ZMod n} {S : Finset (ZMod n)}
    (hS : S.image (a + ·) = S) : ∀ (m : ℕ) (x : ZMod n), x ∈ S → m • a + x ∈ S := by
  intro m
  induction m with
  | zero =>
      intro x hx
      simpa using hx
  | succ m ih =>
      intro x hx
      have h1 : a + (m • a + x) ∈ S.image (a + ·) :=
        Finset.mem_image_of_mem _ (ih x hx)
      rw [hS] at h1
      have h2 : (m + 1) • a + x = a + (m • a + x) := by
        rw [succ_nsmul, add_assoc, add_left_comm]
      rw [h2]
      exact h1

end Rotation

/-! ### The orbit projection `ZMod n →+* ZMod g` -/

section Projection

variable {n g d : ℕ} [NeZero n] [NeZero g]

/-- Reduction of residues modulo a divisor `g` of `n = g * d`.  This concrete ring map is used
below as a model of the space of orbits of translation by an element of additive order `d`;
working with it instead of a quotient type keeps `Fintype` and `DecidableEq` structural. -/
def zmodProj (hn : n = g * d) : ZMod n →+* ZMod g :=
  ZMod.castHom (⟨d, hn⟩ : g ∣ n) (ZMod g)

/-- The orbit projection is surjective. -/
theorem zmodProj_surjective (hn : n = g * d) : Function.Surjective (zmodProj hn) :=
  ZMod.castHom_surjective _

/-- The orbit projection is reduction of natural numbers. -/
theorem zmodProj_natCast (hn : n = g * d) (m : ℕ) :
    zmodProj hn (m : ZMod n) = (m : ZMod g) :=
  map_natCast (zmodProj hn) m

/-- An element of additive order `d` lies in the kernel of the projection to `ZMod g`.  This is
the step at which the source's implicit gcd computation is replaced by an exact divisibility. -/
theorem zmodProj_eq_zero (hn : n = g * d) (hd : 0 < d) {a : ZMod n}
    (ha : addOrderOf a = d) : zmodProj hn a = 0 := by
  have hval : ((a.val : ℕ) : ZMod n) = a := ZMod.natCast_rightInverse a
  have h0 : d • a = 0 := by
    rw [← ha]
    exact addOrderOf_nsmul_eq_zero a
  have h1 : ((d * a.val : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_mul, hval, ← nsmul_eq_mul]
    exact h0
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h1
  have h3 : d * a.val = d * (g * c) := by
    rw [hc, hn]
    ring
  have h4 : g ∣ a.val := ⟨c, Nat.eq_of_mul_eq_mul_left hd h3⟩
  calc zmodProj hn a = zmodProj hn ((a.val : ℕ) : ZMod n) := by rw [hval]
    _ = ((a.val : ℕ) : ZMod g) := zmodProj_natCast hn a.val
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h4

/-- Every natural multiple of an element of additive order `d` lies in the kernel. -/
theorem zmodProj_nsmul (hn : n = g * d) (hd : 0 < d) {a : ZMod n} (ha : addOrderOf a = d)
    (m : ℕ) : zmodProj hn (m • a) = 0 := by
  rw [nsmul_eq_mul, map_mul, zmodProj_eq_zero hn hd ha, mul_zero]

/-- Membership in a fibre of the orbit projection. -/
theorem mem_filter_zmodProj (hn : n = g * d) (y : ZMod g) (x : ZMod n) :
    x ∈ Finset.univ.filter (fun x : ZMod n => zmodProj hn x = y) ↔ zmodProj hn x = y := by
  simp

/-- All fibres of the orbit projection have the same size: translation by a preimage of `y`
carries the fibre over `0` onto the fibre over `y`. -/
theorem card_filter_zmodProj_eq (hn : n = g * d) (y : ZMod g) :
    #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = y)
      = #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = 0) := by
  obtain ⟨c, hc⟩ := zmodProj_surjective hn y
  refine Finset.card_nbij' (fun x => x - c) (fun x => x + c) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : zmodProj hn x = y := (mem_filter_zmodProj hn y x).mp (Finset.mem_coe.mp hx)
    have h1 : zmodProj hn (x - c) = 0 := by rw [map_sub, hx', hc, sub_self]
    exact Finset.mem_coe.mpr ((mem_filter_zmodProj hn 0 (x - c)).mpr h1)
  · intro x hx
    have hx' : zmodProj hn x = 0 := (mem_filter_zmodProj hn 0 x).mp (Finset.mem_coe.mp hx)
    have h1 : zmodProj hn (x + c) = y := by rw [map_add, hx', hc, zero_add]
    exact Finset.mem_coe.mpr ((mem_filter_zmodProj hn y (x + c)).mpr h1)
  · intro x _
    show x - c + c = x
    simp
  · intro x _
    show x + c - c = x
    simp

/-- Every fibre of the orbit projection has exactly `d` elements.  The size is obtained by
counting the whole of `ZMod n` fibrewise, never by `ZMod.val` arithmetic. -/
theorem card_filter_zmodProj (hn : n = g * d) (y : ZMod g) :
    #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = y) = d := by
  have hgpos : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  have h2 : ∀ b ∈ (Finset.univ : Finset (ZMod g)),
      #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = b)
        = #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = 0) :=
    fun b _ => card_filter_zmodProj_eq hn b
  have h1 : #(Finset.univ : Finset (ZMod n))
      = ∑ b ∈ (Finset.univ : Finset (ZMod g)),
          #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = b) :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  rw [Finset.sum_const_nat h2] at h1
  simp only [Finset.card_univ, ZMod.card] at h1
  have h3 : g * d = g * #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = 0) := by
    rw [← hn]
    exact h1
  have h4 : #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = 0) = d :=
    (Nat.eq_of_mul_eq_mul_left hgpos h3).symm
  rw [card_filter_zmodProj_eq hn y, h4]

/-- **The fibres are the orbits.**  The kernel of the orbit projection consists exactly of the
natural multiples of `a`, for any `a` of additive order `d`. -/
theorem zmodProj_eq_zero_iff (hn : n = g * d) (hd : 0 < d) {a : ZMod n}
    (ha : addOrderOf a = d) (x : ZMod n) :
    zmodProj hn x = 0 ↔ ∃ m : ℕ, x = m • a := by
  have hinj : Set.InjOn (fun m : ℕ => m • a) ↑(Finset.range d) := by
    rw [Finset.coe_range, ← ha]
    exact nsmul_injOn_Iio_addOrderOf
  have hsub : (Finset.range d).image (fun m : ℕ => m • a)
      ⊆ Finset.univ.filter (fun x : ZMod n => zmodProj hn x = 0) := by
    intro z hz
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hz
    have hz0 : zmodProj hn z = 0 := by
      rw [← hm]
      exact zmodProj_nsmul hn hd ha m
    exact (mem_filter_zmodProj hn 0 z).mpr hz0
  have e1 : #((Finset.range d).image fun m : ℕ => m • a) = d := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have e2 : #(Finset.univ.filter fun x : ZMod n => zmodProj hn x = 0) = d :=
    card_filter_zmodProj hn 0
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · intro hx
    have hmem : x ∈ (Finset.range d).image fun m : ℕ => m • a := by
      rw [heq]
      exact (mem_filter_zmodProj hn 0 x).mpr hx
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hmem
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    exact zmodProj_nsmul hn hd ha m

/-! ### Invariance is saturation -/

/-- **Translation invariance equals saturation.**  A finite subset of `ZMod n` is invariant
under translation by an element `a` of additive order `d` exactly when it is a union of fibres
of the orbit projection.  This is the source's "a subset is fixed precisely when it is a union
of these orbits", which the source asserts without proof. -/
theorem image_add_eq_iff (hn : n = g * d) (hd : 0 < d) {a : ZMod n} (ha : addOrderOf a = d)
    (S : Finset (ZMod n)) :
    S.image (a + ·) = S ↔
      ∀ x ∈ S, ∀ y : ZMod n, zmodProj hn y = zmodProj hn x → y ∈ S := by
  constructor
  · intro hS x hx y hy
    have h0 : zmodProj hn (y - x) = 0 := by rw [map_sub, hy, sub_self]
    obtain ⟨m, hm⟩ := (zmodProj_eq_zero_iff hn hd ha (y - x)).mp h0
    have hy' : y = m • a + x := by
      rw [← hm]
      ring
    rw [hy']
    exact nsmul_add_mem_of_image_add_eq hS m x hx
  · intro h
    have hsub : S.image (a + ·) ⊆ S := by
      intro z hz
      obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
      have hax : a + x = z := hxz
      have hz' : zmodProj hn z = zmodProj hn x := by
        rw [← hax, map_add, zmodProj_eq_zero hn hd ha, zero_add]
      exact h x hx z hz'
    refine Finset.eq_of_subset_of_card_le hsub ?_
    exact le_of_eq (Finset.card_image_of_injective S (add_right_injective a)).symm

/-- The union of the fibres of the orbit projection lying over a set `T` of residues. -/
def saturate (hn : n = g * d) (T : Finset (ZMod g)) : Finset (ZMod n) :=
  Finset.univ.filter fun x => zmodProj hn x ∈ T

/-- Membership in a saturation. -/
@[simp] theorem mem_saturate (hn : n = g * d) (T : Finset (ZMod g)) (x : ZMod n) :
    x ∈ saturate hn T ↔ zmodProj hn x ∈ T := by
  simp [saturate]

/-- A saturation is `d` times as large as the set of residues it lies over. -/
theorem card_saturate (hn : n = g * d) (T : Finset (ZMod g)) :
    #(saturate hn T) = #T * d := by
  have h1 : #(saturate hn T)
      = ∑ b ∈ T, #(Finset.filter (fun x => zmodProj hn x = b) (saturate hn T)) :=
    Finset.card_eq_sum_card_fiberwise fun x hx =>
      Finset.mem_coe.mpr ((mem_saturate hn T x).mp (Finset.mem_coe.mp hx))
  have h2 : ∀ b ∈ T, #(Finset.filter (fun x => zmodProj hn x = b) (saturate hn T)) = d := by
    intro b hb
    have hfe : Finset.filter (fun x => zmodProj hn x = b) (saturate hn T)
        = Finset.univ.filter fun x : ZMod n => zmodProj hn x = b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_saturate]
      constructor
      · rintro ⟨-, hx⟩
        exact hx
      · intro hx
        exact ⟨by rw [hx]; exact hb, hx⟩
    rw [hfe, card_filter_zmodProj hn b]
  rw [h1, Finset.sum_const_nat h2]

/-- Saturating a set of residues recovers it under the orbit projection. -/
theorem image_zmodProj_saturate (hn : n = g * d) (T : Finset (ZMod g)) :
    (saturate hn T).image (zmodProj hn) = T := by
  ext y
  simp only [Finset.mem_image, mem_saturate]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    exact hx
  · intro hy
    obtain ⟨x, hx⟩ := zmodProj_surjective hn y
    exact ⟨x, by rw [hx]; exact hy, hx⟩

/-- A translation-invariant subset is the saturation of its image of residues. -/
theorem saturate_image_zmodProj (hn : n = g * d) (hd : 0 < d) {a : ZMod n}
    (ha : addOrderOf a = d) {S : Finset (ZMod n)} (hS : S.image (a + ·) = S) :
    saturate hn (S.image (zmodProj hn)) = S := by
  have h := (image_add_eq_iff hn hd ha S).mp hS
  ext y
  simp only [mem_saturate, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact h x hx y hxy.symm
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Every saturation is translation invariant. -/
theorem image_add_saturate (hn : n = g * d) (hd : 0 < d) {a : ZMod n} (ha : addOrderOf a = d)
    (T : Finset (ZMod g)) : (saturate hn T).image (a + ·) = saturate hn T := by
  refine (image_add_eq_iff hn hd ha _).mpr ?_
  intro x hx y hy
  rw [mem_saturate] at hx ⊢
  rw [hy]
  exact hx

end Projection

/-! ### The fixed-point count -/

section FixedPoints

variable {n : ℕ} [NeZero n]

/-- The `k`-element subsets of `ZMod n` fixed by translation by `a`. -/
def rotationFix (k : ℕ) (a : ZMod n) : Finset (Finset (ZMod n)) :=
  ((Finset.univ : Finset (ZMod n)).powersetCard k).filter fun S => S.image (a + ·) = S

/-- Membership in the set of fixed `k`-subsets. -/
@[simp] theorem mem_rotationFix (k : ℕ) (a : ZMod n) (S : Finset (ZMod n)) :
    S ∈ rotationFix k a ↔ #S = k ∧ S.image (a + ·) = S := by
  simp [rotationFix]

variable {g d : ℕ} [NeZero g]

/-- **The fixed-point count**, equation (16.8) of the source, for an arbitrary group element.
If `a : ZMod n` has additive order `d` and `n = g * d`, then the number of `k`-element subsets
of `ZMod n` invariant under translation by `a` is `g.choose (k / d)` when `d ∣ k`, and `0`
otherwise.  No hypothesis `k ≤ n` is needed. -/
theorem card_rotationFix (hn : n = g * d) (hd : 0 < d) {a : ZMod n} (ha : addOrderOf a = d)
    (k : ℕ) : #(rotationFix k a) = if d ∣ k then g.choose (k / d) else 0 := by
  by_cases hdk : d ∣ k
  · rw [if_pos hdk]
    have hbij : #(rotationFix k a)
        = #((Finset.univ : Finset (ZMod g)).powersetCard (k / d)) := by
      refine Finset.card_nbij' (fun S => S.image (zmodProj hn)) (saturate hn) ?_ ?_ ?_ ?_
      · intro S hS
        obtain ⟨hcard, hinv⟩ := (mem_rotationFix k a S).mp (Finset.mem_coe.mp hS)
        have h1 := saturate_image_zmodProj hn hd ha hinv
        have h2 : #(saturate hn (S.image (zmodProj hn))) = #(S.image (zmodProj hn)) * d :=
          card_saturate hn _
        rw [h1, hcard] at h2
        refine Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩)
        have h3 : k / d * d = #(S.image (zmodProj hn)) * d := by
          rw [Nat.div_mul_cancel hdk, h2]
        exact (Nat.eq_of_mul_eq_mul_right hd h3).symm
      · intro T hT
        obtain ⟨-, hTc⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)
        refine Finset.mem_coe.mpr
          ((mem_rotationFix k a _).mpr ⟨?_, image_add_saturate hn hd ha T⟩)
        rw [card_saturate hn T, hTc, Nat.div_mul_cancel hdk]
      · intro S hS
        exact saturate_image_zmodProj hn hd ha
          ((mem_rotationFix k a S).mp (Finset.mem_coe.mp hS)).2
      · intro T _
        exact image_zmodProj_saturate hn T
    rw [hbij, Finset.card_powersetCard, Finset.card_univ, ZMod.card]
  · rw [if_neg hdk, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro S hS
    obtain ⟨hcard, hinv⟩ := (mem_rotationFix k a S).mp hS
    have h1 := saturate_image_zmodProj hn hd ha hinv
    have h2 : #(saturate hn (S.image (zmodProj hn))) = #(S.image (zmodProj hn)) * d :=
      card_saturate hn _
    rw [h1, hcard] at h2
    exact hdk ⟨#(S.image (zmodProj hn)), by rw [h2, mul_comm]⟩

end FixedPoints

/-! ### The algebraic half -/

section Algebraic

/-- **The order of `ω ^ j`.**  If `ω` is a primitive `n`-th root of unity, then `ω ^ j` is a
primitive root of unity whose order is the additive order of `j` in `ZMod n`, that is, the
order of translation by `j`.  This is the source's unproved sentence "the number `ω^j` is a
primitive `d`th root", and it is exactly what identifies the combinatorial `d` with the
algebraic one.  Only a `CommMonoid` is needed; there is no `NeZero n` hypothesis. -/
theorem isPrimitiveRoot_pow_addOrderOf {M : Type*} [CommMonoid M] {n : ℕ} {ω : M}
    (hω : IsPrimitiveRoot ω n) (j : ℕ) :
    IsPrimitiveRoot (ω ^ j) (addOrderOf ((j : ZMod n))) := by
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, hω.pow_eq_one_iff_dvd, mul_comm]
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_mul, ← nsmul_eq_mul]
    exact addOrderOf_nsmul_eq_zero _
  · intro l hl
    rw [← pow_mul, hω.pow_eq_one_iff_dvd] at hl
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff, mul_comm]
    exact hl

/-- Evaluating the universal Gaussian coefficient `[n,k]_X ∈ R[X]` at `r` gives `[n,k]_r`.
Valid over every commutative ring; no domain hypothesis. -/
theorem eval_gaussianBinomial_X {R : Type*} [CommRing R] (r : R) (n k : ℕ) :
    Polynomial.eval r (gaussianBinomial (Polynomial.X : Polynomial R) n k)
      = gaussianBinomial r n k := by
  have h := map_gaussianBinomial (Polynomial.evalRingHom r) (Polynomial.X : Polynomial R) n k
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_X] at h
  exact h

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Value of a Gaussian coefficient at a primitive `d`-th root of unity** on a row that is a
multiple of `d`: `[g d, k]_ζ = \binom g{k/d}` if `d ∣ k`, and `0` otherwise.  This is the
specialisation of `Fabius.gaussianBinomial_q_lucas` used in the source proof.  It is total in
`k`: for `k > g * d` both sides vanish. -/
theorem gaussianBinomial_isPrimitiveRoot_mul {ζ : R} {d : ℕ} (hd : 0 < d)
    (hζ : IsPrimitiveRoot ζ d) (g k : ℕ) :
    gaussianBinomial ζ (g * d) k = if d ∣ k then (g.choose (k / d) : R) else 0 := by
  have h := gaussianBinomial_q_lucas hd hζ g (k / d) (b := 0) (s := k % d) hd
    (Nat.mod_lt _ hd)
  rw [add_zero, Nat.div_add_mod'] at h
  by_cases hdk : d ∣ k
  · rw [if_pos hdk, h, Nat.mod_eq_zero_of_dvd hdk, gaussianBinomial_zero_zero, mul_one]
  · rw [if_neg hdk, h]
    have hne : k % d ≠ 0 := fun hh => hdk (Nat.dvd_of_mod_eq_zero hh)
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hr, gaussianBinomial_zero_succ, mul_zero]

end Algebraic

/-! ### Cyclic sieving -/

section CyclicSieving

/-- **The cyclic sieving phenomenon.**  A triple `(s, σ, F)` — a finite set `s : Finset α`, a
permutation `σ` generating the acting cyclic group, and a polynomial `F` — exhibits cyclic
sieving with respect to `ω : R` when `#Fix(σ ^ j) = F(ω ^ j)` for every `j : ℕ`.

Mathlib has no cyclic-sieving API, so the predicate is introduced here.  Two deliberate
differences from the informal definition in the source: the ambient ring `R` in which the
equality is asserted is an explicit parameter (the source writes `#Fix(c^j) = F(ω^j)` with a
natural number on the left and an element of `ℤ[ω]` on the right, under an evident coercion),
and the primitivity of `ω` is not built in but supplied by the user of the predicate.  No
independence of the choice of primitive root is claimed. -/
def IsCyclicSieving {α : Type*} [DecidableEq α] (s : Finset α) (σ : Equiv.Perm α)
    {R : Type*} [CommRing R] (ω : R) (F : Polynomial R) : Prop :=
  ∀ j : ℕ, (#(s.filter fun x => (σ ^ j) x = x) : R) = Polynomial.eval (ω ^ j) F

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n] {ω : R}

/-- **Cyclic sieving for `k`-subsets, unpackaged.**  For a primitive `n`-th root of unity `ω`
in a commutative integral domain, the number of `k`-element subsets of `ZMod n` invariant under
translation by `j` equals the Gaussian coefficient `[n, k]` evaluated at `ω ^ j`.

This is the whole content of the source theorem; the packaged form
`isCyclicSieving_powersetCard` merely rewrites the fixed-point set of `rotation 1 ^ j`.  The
statement is total in `k` and in `j`. -/
theorem card_rotationFix_cast (hω : IsPrimitiveRoot ω n) (k j : ℕ) :
    (#(rotationFix k ((j : ZMod n))) : R) = gaussianBinomial (ω ^ j) n k := by
  obtain ⟨d, hd_def⟩ : ∃ d, addOrderOf ((j : ZMod n)) = d := ⟨_, rfl⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hdvd : d ∣ n := by
    rw [← hd_def, addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn0
  obtain ⟨g, hg⟩ : ∃ g, n = g * d := ⟨n / d, (Nat.div_mul_cancel hdvd).symm⟩
  haveI : NeZero g := ⟨by
    rintro rfl
    rw [zero_mul] at hg
    exact (NeZero.ne n) hg⟩
  have hζ : IsPrimitiveRoot (ω ^ j) d := by
    rw [← hd_def]
    exact isPrimitiveRoot_pow_addOrderOf hω j
  rw [card_rotationFix hg hdpos hd_def k, hg,
    gaussianBinomial_isPrimitiveRoot_mul hdpos hζ g k]
  split_ifs with hdk <;> simp

/-- **Cyclic sieving for `k`-subsets** (`thm:csp-subsets`).  For every `n > 0`, every `k : ℕ`,
every commutative integral domain `R` and every primitive `n`-th root of unity `ω : R`, the
triple consisting of the `k`-element subsets of `ZMod n`, the translation action of the cyclic
group generated by `1`, and the Gaussian coefficient `[n, k]_q` exhibits the cyclic sieving
phenomenon. -/
theorem isCyclicSieving_powersetCard (hω : IsPrimitiveRoot ω n) (k : ℕ) :
    IsCyclicSieving ((Finset.univ : Finset (ZMod n)).powersetCard k) (rotation (1 : ZMod n)) ω
      (gaussianBinomial (Polynomial.X : Polynomial R) n k) := by
  intro j
  have hj1 : j • (1 : ZMod n) = (j : ZMod n) := by
    rw [nsmul_eq_mul, mul_one]
  have hfil : (((Finset.univ : Finset (ZMod n)).powersetCard k).filter
        fun S => (rotation (1 : ZMod n) ^ j) S = S)
      = rotationFix k ((j : ZMod n)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      mem_rotationFix]
    constructor
    · rintro ⟨h1, h2⟩
      rw [rotation_pow_apply, hj1, rotation_apply] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [rotation_pow_apply, hj1, rotation_apply]
      exact h2
  rw [hfil, eval_gaussianBinomial_X]
  exact card_rotationFix_cast hω k j

end CyclicSieving

end Fabius
