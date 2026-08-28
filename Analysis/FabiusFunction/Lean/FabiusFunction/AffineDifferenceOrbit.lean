import FabiusFunction.ThueMorseBitSupport
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Affine-difference iterates and derivative orbits

This module isolates the finite algebra behind two-branch differential
refinement equations.  For

`Δ_{b,c} f (z) = f (b*z+c) - f (b*z-c)`,

the `n`-fold iterate is a signed sum over the Boolean cube.  If an open set is
invariant under both affine branches and `f' = a • Δ_{b,c} f` there, the same
finite orbit gives every iterated derivative, with the exact chain-rule factor
`a^n b^(n choose 2)`.  No global smoothness hypothesis is needed: the
one-step derivative identity bootstraps all differentiability used in the
proof.

The specialization `b = 2`, `c = 1` reindexes the Boolean cube by binary
support and gives the usual finite Thue--Morse affine orbit.  The generic
results are valid for functions into an arbitrary normed space over a
nontrivially normed field.

## Main results

* `affineDifference_iterate_apply` expands every finite iterate over a
  powerset.
* `iteratedDeriv_eq_affineDifference_iterate_on` propagates a one-step
  derivative identity on an invariant open set.
* `affineDifference_iterate_two_one_apply` is the dyadic Thue--Morse form.
-/

set_option autoImplicit false

open Finset Set
open scoped BigOperators

namespace Fabius

section Algebra

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E]

/-- The two-branch affine difference
`f (b*z+c) - f (b*z-c)`. -/
def affineDifference (b c : 𝕜) (f : 𝕜 → E) (z : 𝕜) : E :=
  f (b * z + c) - f (b * z - c)

/-- The affine point indexed by a Boolean-cube vertex `T`.

The first sum is the all-positive geometric shift; membership in `T` flips
the corresponding digit, which subtracts twice that power.  In applications
`T` is a subset of `range n`. -/
def affineCubePoint (b c : 𝕜) (n : ℕ) (T : Finset ℕ) (z : 𝕜) : 𝕜 :=
  b ^ n * z + c *
    (∑ k ∈ range n, b ^ k) - 2 * c * (∑ k ∈ T, b ^ k)

private theorem affineCubePoint_succ_notMem
    (b c : 𝕜) (n : ℕ) {T : Finset ℕ} (hT : T ⊆ range n) (z : 𝕜) :
    affineCubePoint b c (n + 1) T z =
      affineCubePoint b c n T (b * z + c) := by
  have hnT : n ∉ T := by
    intro hn
    exact (Nat.lt_irrefl n) (mem_range.mp (hT hn))
  simp only [affineCubePoint, sum_range_succ, pow_succ]
  ring

private theorem affineCubePoint_succ_insert
    (b c : 𝕜) (n : ℕ) {T : Finset ℕ} (hT : T ⊆ range n) (z : 𝕜) :
    affineCubePoint b c (n + 1) (insert n T) z =
      affineCubePoint b c n T (b * z - c) := by
  have hnT : n ∉ T := by
    intro hn
    exact (Nat.lt_irrefl n) (mem_range.mp (hT hn))
  simp only [affineCubePoint, sum_range_succ, sum_insert hnT, pow_succ]
  ring

/-- A constant scalar commutes with every iterate of an affine difference. -/
theorem affineDifference_iterate_const_smul
    [Module 𝕜 E] (b c a : 𝕜) (f : 𝕜 → E) (n : ℕ) :
    (affineDifference b c)^[n] (fun z => a • f z) =
      fun z => a • ((affineDifference b c)^[n] f) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext z
      simp only [affineDifference, smul_sub]

/-- **Boolean-cube formula for an affine-difference iterate.**  The result is
pure finite algebra: it needs no topology, differentiability, or division. -/
theorem affineDifference_iterate_apply
    (b c : 𝕜) (f : 𝕜 → E) (n : ℕ) (z : 𝕜) :
    ((affineDifference b c)^[n] f) z =
      ∑ T ∈ (range n).powerset,
        ((-1 : ℤ) ^ T.card) • f (affineCubePoint b c n T z) := by
  classical
  induction n generalizing z with
  | zero => simp [affineCubePoint]
  | succ n ih =>
      rw [Function.iterate_succ_apply', affineDifference, ih, ih]
      rw [Finset.range_add_one]
      rw [Finset.powerset_insert (range n) n]
      have hdisj : Disjoint (range n).powerset
          ((range n).powerset.image (insert n)) := by
        rw [Finset.disjoint_left]
        intro T hT hTi
        rcases mem_image.mp hTi with ⟨U, hU, rfl⟩
        have hsub := mem_powerset.mp hT
        have : n ∈ range n := hsub (mem_insert_self n U)
        simp at this
      rw [sum_union hdisj]
      rw [sum_image]
      · rw [← sum_sub_distrib]
        rw [← sum_add_distrib]
        refine sum_congr rfl fun T hT => ?_
        have hsub : T ⊆ range n := mem_powerset.mp hT
        have hnT : n ∉ T := by
          intro hn
          exact (Nat.lt_irrefl n) (mem_range.mp (hsub hn))
        rw [affineCubePoint_succ_notMem b c n hsub z,
          affineCubePoint_succ_insert b c n hsub z,
          card_insert_of_notMem hnT, pow_succ]
        simp only [mul_neg, mul_one, neg_smul, sub_eq_add_neg]
      · intro T hT U hU hEq
        have hnT : n ∉ T := by
          intro hn
          exact (Nat.lt_irrefl n)
            (mem_range.mp ((mem_powerset.mp hT) hn))
        have hnU : n ∉ U := by
          intro hn
          exact (Nat.lt_irrefl n)
            (mem_range.mp ((mem_powerset.mp hU) hn))
        have hErase := congrArg (fun V : Finset ℕ => V.erase n) hEq
        simpa [hnT, hnU] using hErase

end Algebra

section Calculus

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem hasDerivAt_affineDifference_iterate
    {s : Set 𝕜} {b c : 𝕜}
    (hp : MapsTo (fun z : 𝕜 => b * z + c) s s)
    (hm : MapsTo (fun z : 𝕜 => b * z - c) s s)
    {f f' : 𝕜 → E}
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (n : ℕ) {z : 𝕜} (hz : z ∈ s) :
    HasDerivAt ((affineDifference b c)^[n] f)
      (b ^ n • ((affineDifference b c)^[n] f') z) z := by
  induction n generalizing z with
  | zero => simpa using hf z hz
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hplus := (ih (hp hz)).scomp z
        (((hasDerivAt_id z).const_mul b).add_const c)
      have hminus := (ih (hm hz)).scomp z
        (((hasDerivAt_id z).const_mul b).sub_const c)
      have hraw := hplus.sub hminus
      have hfun : affineDifference b c ((affineDifference b c)^[n] f) =
          (((affineDifference b c)^[n] f) ∘ fun x => b * id x + c) -
            (((affineDifference b c)^[n] f) ∘ fun x => b * id x - c) := by
        funext y
        rfl
      rw [hfun]
      convert hraw using 1
      rw [Function.iterate_succ_apply', affineDifference, pow_succ, smul_sub]
      simp only [smul_smul, mul_one]
      rw [mul_comm (b ^ n) b]

/-- **All-order affine-difference derivative propagation on an open invariant
domain.**  If both affine branches preserve `s` and
`f' = a • (f(bz+c)-f(bz-c))` on `s`, then every derivative is the matching
finite operator iterate with coefficient `a^n b^(n choose 2)`.

The one-step `HasDerivAt` hypothesis supplies all regularity needed by the
induction; no separate `ContDiff` assumption is imposed. -/
theorem iteratedDeriv_eq_affineDifference_iterate_on
    {s : Set 𝕜} (hs : IsOpen s) {a b c : 𝕜}
    (hp : MapsTo (fun z : 𝕜 => b * z + c) s s)
    (hm : MapsTo (fun z : 𝕜 => b * z - c) s s)
    (f : 𝕜 → E)
    (hD : ∀ z ∈ s,
      HasDerivAt f (a • affineDifference b c f z) z)
    (n : ℕ) {z : 𝕜} (hz : z ∈ s) :
    iteratedDeriv n f z =
      (a ^ n * b ^ n.choose 2) •
        ((affineDifference b c)^[n] f) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n f =ᶠ[nhds z]
          (a ^ n * b ^ n.choose 2) •
            ((affineDifference b c)^[n] f) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        simpa only [Pi.smul_apply] using ih hy
      rw [heq.deriv_eq]
      have horbit := hasDerivAt_affineDifference_iterate hp hm hD n hz
      have hscaled := horbit.const_smul (a ^ n * b ^ n.choose 2)
      rw [affineDifference_iterate_const_smul,
        ← Function.iterate_succ_apply] at hscaled
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [Nat.choose_succ_succ]
        simp [add_comm]
      rw [hscaled.deriv, hchoose, pow_succ, pow_add]
      simp only [smul_smul]
      congr 1
      ring

/-- Global form of `iteratedDeriv_eq_affineDifference_iterate_on`. -/
theorem iteratedDeriv_eq_affineDifference_iterate
    {a b c : 𝕜} (f : 𝕜 → E)
    (hD : ∀ z : 𝕜,
      HasDerivAt f (a • affineDifference b c f z) z)
    (n : ℕ) (z : 𝕜) :
    iteratedDeriv n f z =
      (a ^ n * b ^ n.choose 2) •
        ((affineDifference b c)^[n] f) z := by
  exact iteratedDeriv_eq_affineDifference_iterate_on isOpen_univ
    (mapsTo_univ _ _) (mapsTo_univ _ _) f (fun y _ => hD y) n (mem_univ z)

end Calculus

section Dyadic

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E]

/-- **Dyadic Thue--Morse form of the affine-difference iterate.**  The shift
is evaluated in the coefficient ring, so there is no truncated natural
subtraction in `2^n - 1 - 2j`. -/
theorem affineDifference_iterate_two_one_apply
    (f : 𝕜 → E) (n : ℕ) (z : 𝕜) :
    ((affineDifference (2 : 𝕜) 1)^[n] f) z =
      ∑ j ∈ range (2 ^ n), thueMorseSign j •
        f ((2 : 𝕜) ^ n * z + (2 : 𝕜) ^ n - 1 - 2 * (j : 𝕜)) := by
  classical
  rw [affineDifference_iterate_apply]
  rw [← sum_powerset_two_pow n (fun j => thueMorseSign j •
    f ((2 : 𝕜) ^ n * z + (2 : 𝕜) ^ n - 1 - 2 * (j : 𝕜)))]
  refine sum_congr rfl fun T hT => ?_
  rw [thueMorseSign_sum_two_pow]
  congr 1
  unfold affineCubePoint
  have hgeom : ∑ k ∈ range n, (2 : 𝕜) ^ k = (2 : 𝕜) ^ n - 1 := by
    have h := geom_sum_mul (2 : 𝕜) n
    norm_num at h
    exact h
  have hcast :
      ((∑ k ∈ T, 2 ^ k : ℕ) : 𝕜) = ∑ k ∈ T, (2 : 𝕜) ^ k := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert k T hk _ => simp [hk]
  rw [hgeom]
  rw [hcast]
  ring_nf

end Dyadic

end Fabius
