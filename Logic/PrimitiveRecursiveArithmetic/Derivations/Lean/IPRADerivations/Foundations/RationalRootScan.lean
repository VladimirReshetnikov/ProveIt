import IPRADerivations.Foundations.RationalRootConstant
import IPRADerivations.Foundations.EigenvalueGrid
import IPRADerivations.Foundations.FilteredEnumeration

/-!
# The bounded rational-root scan (`ipra_presentations_to_witnesses`, `lem:norm-rational-roots`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-rational-roots`: with
`B(H) = max{1, |c_0|, |c_d|}` (RR1), "define `Roots_ℚ(H)` by scanning all pairs
`-B(H) ≤ p ≤ B(H)`, `1 ≤ q ≤ B(H)`, `gcd(|p|, q) = 1`, and retaining `p/q` exactly when
`H(p/q) = 0`. Each retained rational has a unique representation in this scan. ... the displayed
procedure returns exactly its rational roots, without repetition. Every root has reduced
numerator and denominator bounded in absolute value by `B(H)`." Proof: "Soundness follows from
the final exact substitution test. ... If `p = 0`, reducedness gives `q = 1`, so the scan
includes it. ... For `d = 0`, this contradicts `c_0 ≠ 0` ... `|p| ≤ |c_0|` and `q ≤ |c_d|`. Thus
every root occurs in the scan."

`Foundations/RationalRootDegree` and `Foundations/RationalRootConstant` have the divisibility
step and the two bounds. This module derives the scan, in natural-number form (`p`, `q` are
`|p|` and `q`; signs are split into the two coefficient lists `a`, `b` as there):

* `mx`, `le_mx_left`, `le_mx_right`, `height`: the bound `B(H) = max{1, |c_0|, |c_d|}`;
* `bez_swap`: a Bezout relation between `p` and `q` read in the other orientation;
* `root_box`: a root `p/q` with `p ≠ 0`, `c_0 ≠ 0`, `c_d ≠ 0` has `p ≤ B(H)` and `q ≤ B(H)`;
* `zero_root_den`: a reduced fraction with numerator `0` has denominator `1`;
* `const_eval`, `const_no_root`: for `d = 0` the cleared equation is `a_0 = b_0`, that is
  `c_0 = 0`;
* `reduced_unique`: two reduced fractions with `p q₂ = p₂ q` have `q = q₂` and `p = p₂`: the
  unique representation in the scan;
* `pair_lt_box`: pairs with both entries at most `B` have codes below `box B`;
* `scan_sound`, `scan_complete`, `scan_nodup`: for any test `K(⟨p, q⟩, y)`, the list
  `r ↦ sel K r (box B) y`, `r < ℓ = rank K (box B) y` (the rank/select enumeration of
  `Foundations/FilteredEnumeration`) consists of retained pairs, contains every retained pair
  with entries at most `B`, and has no repetition;
* `roots_complete`, `zero_root_complete`: every root passing the test occurs in the list with
  `B = B(H)`.

The test `K` is a parameter: the statements hold for the exact substitution test (and for it
conjoined with the coprimality test). A negative numerator is the same scan for the
polynomial `H(-T)`, whose two coefficient lists are those of `H` with the odd-index entries
exchanged. Not derived: clearing the denominators of a rational polynomial, the removal of the
factor `T^e`, and the evaluation of `K` as a primitive recursive program on coefficient codes.
-/

namespace LeanProofs.IPRA.Foundations.RationalRootScan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RationalRootDegree (Bez euclid P tB top_at)
open LeanProofs.IPRA.Foundations.RationalRootConstant (num_bound den_bound)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The height bound -/

/-- `max(a, b) = a + (b ∸ a)`. -/
abbrev mx (a b : PTm k) : PTm k := a + monus b a

theorem le_mx_left (a b : PTm k) : Γ ⊢[PRAAx] le a (mx a b) := le_add_right a _

theorem le_mx_right (a b : PTm k) : Γ ⊢[PRAAx] le b (mx a b) :=
  .orE (le_total a b) (le_congr (.eqRefl b) (eq_add_of_le Prf.hyp0) (le_refl b))
    (le_trans Prf.hyp0 (le_add_right a _))

/-- `|a_i - b_i|`, the absolute value of the coefficient `c_i = a_i - b_i`. -/
abbrev absd (a b : PTm 2) (i x : PTm k) : PTm k :=
  monus (inst2 a i x) (inst2 b i x) + monus (inst2 b i x) (inst2 a i x)

/-- (RR1): `B(H) = max{1, |c_0|, |c_d|}`. -/
abbrev height (a b : PTm 2) (d x : PTm k) : PTm k := mx one (mx (absd a b zero x) (absd a b d x))

/-- A Bezout relation between `p` and `q`, read with the roles exchanged. -/
theorem bez_swap {p' q' u v : PTm k} (h : Γ ⊢[PRAAx] Bez p' (succ q') u v) :
    Γ ⊢[PRAAx] Bez q' (succ p') v u :=
  .orE h (.orI₂ (Prf.eqSymm Prf.hyp0)) (.orI₁ (Prf.eqSymm Prf.hyp0))

/-- A root with nonzero numerator lies in the box: `p ≤ B(H)` and `q ≤ B(H)`. -/
theorem root_box (a b : PTm 2) {p' q' u v d x : PTm k}
    (hB : Γ ⊢[PRAAx] Bez p' (succ q') u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') (succ q') d x ≐ P b (succ d) (succ p') (succ q') d x)
    (h0 : Γ ⊢[PRAAx] absd a b zero x ≐ succ (pred (absd a b zero x)))
    (hd : Γ ⊢[PRAAx] absd a b d x ≐ succ (pred (absd a b d x))) :
    Γ ⊢[PRAAx] le (succ p') (height a b d x) ⋏ le (succ q') (height a b d x) :=
  .andI
    (le_trans (num_bound a b hB hE h0) (le_trans (le_mx_left _ _) (le_mx_right _ _)))
    (le_trans (den_bound a b (bez_swap hB) hE hd) (le_trans (le_mx_right _ _) (le_mx_right _ _)))

/-! ## The exceptional cases -/

/-- "If `p = 0`, reducedness gives `q = 1`." -/
theorem zero_root_den {q' u v : PTm k} (hB : Γ ⊢[PRAAx] Bez q' zero u v) :
    Γ ⊢[PRAAx] q' ≐ zero := by
  refine .orE hB ?_ ?_
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := u * succ q' ≐ v * zero + one))
    have h1 : ((u * succ q' ≐ v * zero + one) :: Γ) ⊢[PRAAx] dvd (succ q') one := by
      refine dvd_of_eq (w := u) ?_
      apply deriveNat; ipra_simps
      linear_combination -e
    have h2 := Foundations.RationalRootConstant.dvd_le h1 (pos_of_eq_succ (.eqRefl _))
    exact (monus_zero q').eqSymm.eqTrans ((succ_monus_succ q' zero).eqSymm.eqTrans h2)
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := u * succ q' + one ≐ v * zero))
    refine succ_ne_zero' _ (a := u * succ q') ?_
    apply deriveNat; ipra_simps
    linear_combination e

/-- The homogeneous sum of degree `0` is its constant coefficient. -/
theorem const_eval (a : PTm 2) (p q x : PTm k) :
    Γ ⊢[PRAAx] P a (succ zero) p q zero x ≐ inst2 a zero x := by
  have s := natEq (sum_succ' (Γ := Γ) (tB a) zero (pairT p (pairT q (pairT zero x))))
  have z := natEq (sum_zero (Γ := Γ) (tB a) (pairT p (pairT q (pairT zero x))))
  have t := natEq (top_at (Γ := Γ) a p q zero x)
  have w := natEq (pw_zero (Γ := Γ) p)
  apply deriveNat; ipra_simps
  linear_combination s + z + t + 𝔞 (inst2 a zero x) * w

/-- "For `d = 0`, this contradicts `c_0 ≠ 0`": the cleared equation of degree `0` says
`a_0 = b_0`. -/
theorem const_no_root (a b : PTm 2) {p q x : PTm k}
    (hE : Γ ⊢[PRAAx] P a (succ zero) p q zero x ≐ P b (succ zero) p q zero x) :
    Γ ⊢[PRAAx] inst2 a zero x ≐ inst2 b zero x :=
  (const_eval a p q x).eqSymm.eqTrans (hE.eqTrans (const_eval b p q x))

/-- "Each retained rational has a unique representation": reduced fractions with
`p q₂ = p₂ q` coincide. -/
theorem reduced_unique {p p₂ q' q₂' u v u₂ v₂ : PTm k} (hB : Γ ⊢[PRAAx] Bez q' p u v)
    (hB₂ : Γ ⊢[PRAAx] Bez q₂' p₂ u₂ v₂) (hE : Γ ⊢[PRAAx] p * succ q₂' ≐ p₂ * succ q') :
    Γ ⊢[PRAAx] (succ q' ≐ succ q₂') ⋏ (p ≐ p₂) := by
  have d₁ : Γ ⊢[PRAAx] dvd (succ q') (succ q₂') :=
    euclid hB (dvd_of_eq (w := p₂) ((mul_comm _ _).eqTrans (hE.eqTrans (mul_comm _ _))))
  have d₂ : Γ ⊢[PRAAx] dvd (succ q₂') (succ q') :=
    euclid hB₂ (dvd_of_eq (w := p) ((mul_comm _ _).eqTrans (hE.eqSymm.eqTrans (mul_comm _ _))))
  have e : Γ ⊢[PRAAx] succ q' ≐ succ q₂' :=
    le_antisymm (Foundations.RationalRootConstant.dvd_le d₁ (pos_of_eq_succ (.eqRefl _)))
      (Foundations.RationalRootConstant.dvd_le d₂ (pos_of_eq_succ (.eqRefl _)))
  refine .andI e (Foundations.EigenvalueGrid.mul_cancel (d' := q') ?_)
  exact (mul_comm _ _).eqTrans ((congrMul (.eqRefl p) e).eqTrans (hE.eqTrans (mul_comm _ _)))

/-! ## The scan -/

/-- Pairs with both entries at most `B` have codes below `⟨B, B⟩ + 1`. -/
theorem pair_lt_box {p q B : PTm k} (hp : Γ ⊢[PRAAx] le p B) (hq : Γ ⊢[PRAAx] le q B) :
    Γ ⊢[PRAAx] lt (pairT p q) (succ (pairT B B)) := by
  have ea := natEq (eq_add_of_le hp)
  have eb := natEq (eq_add_of_le hq)
  refine le_of_eq_add (d := (monus B p + monus B q) *
      (p + q + p + q + monus B p + monus B q) + monus B p) ?_
  unfold pairT
  apply deriveNat
  ipra_simps
  linear_combination (2 * 𝔞 B + 𝔞 p + 𝔞 q + 𝔞 (monus B p) + 𝔞 (monus B q)) * (ea + eb) + ea

/-- The number of codes scanned for the bound `B`. -/
abbrev box (B : PTm k) : PTm k := succ (pairT B B)

variable (K : PTm 2)

/-- Soundness: every listed code is below the box and passes the test. -/
theorem scan_sound {r B y : PTm k} (h : Γ ⊢[PRAAx] lt r (rank K (box B) y)) :
    Γ ⊢[PRAAx] lt (sel K r (box B) y) (box B) ⋏
      neg (inst2 K (sel K r (box B) y) y ≐ zero) :=
  .andI (Prf.andE₁ (sel_spec K h)) (Prf.andE₁ (Prf.andE₂ (sel_spec K h)))

/-- Completeness: a retained pair with entries at most `B` is listed, at the index given by
its rank. -/
theorem scan_complete {p q B y : PTm k} (hp : Γ ⊢[PRAAx] le p B) (hq : Γ ⊢[PRAAx] le q B)
    (hk : Γ ⊢[PRAAx] neg (inst2 K (pairT p q) y ≐ zero)) :
    Γ ⊢[PRAAx] lt (rank K (pairT p q) y) (rank K (box B) y) ⋏
      (sel K (rank K (pairT p q) y) (box B) y ≐ pairT p q) :=
  .andI (rank_lt_size K (pair_lt_box hp hq) hk) (sel_rank K (pair_lt_box hp hq) hk)

/-- No repetition: distinct indices list distinct codes. -/
theorem scan_nodup {r r' B y : PTm k} (h : Γ ⊢[PRAAx] lt r (rank K (box B) y))
    (h' : Γ ⊢[PRAAx] lt r' (rank K (box B) y))
    (e : Γ ⊢[PRAAx] sel K r (box B) y ≐ sel K r' (box B) y) : Γ ⊢[PRAAx] r ≐ r' :=
  (Prf.andE₂ (Prf.andE₂ (sel_spec K h))).eqSymm.eqTrans
    ((congrAp2 (sumF (sgB K)) e (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (sel_spec K h'))))

/-- `lem:norm-rational-roots`, completeness for a nonzero numerator: a root passing the test
is listed by the scan of the box of radius `B(H)`. -/
theorem roots_complete (a b : PTm 2) {p' q' u v d x y : PTm k}
    (hB : Γ ⊢[PRAAx] Bez p' (succ q') u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') (succ q') d x ≐ P b (succ d) (succ p') (succ q') d x)
    (h0 : Γ ⊢[PRAAx] absd a b zero x ≐ succ (pred (absd a b zero x)))
    (hd : Γ ⊢[PRAAx] absd a b d x ≐ succ (pred (absd a b d x)))
    (hk : Γ ⊢[PRAAx] neg (inst2 K (pairT (succ p') (succ q')) y ≐ zero)) :
    Γ ⊢[PRAAx] lt (rank K (pairT (succ p') (succ q')) y) (rank K (box (height a b d x)) y) ⋏
      (sel K (rank K (pairT (succ p') (succ q')) y) (box (height a b d x)) y ≐
        pairT (succ p') (succ q')) :=
  scan_complete K (Prf.andE₁ (root_box a b hB hE h0 hd)) (Prf.andE₂ (root_box a b hB hE h0 hd)) hk

/-- Completeness for the numerator `0`: the reduced fraction is `0/1`, which is in every box of
radius at least `1`. -/
theorem zero_root_complete {q' u v B y : PTm k} (hB : Γ ⊢[PRAAx] Bez q' zero u v)
    (h1 : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] neg (inst2 K (pairT zero (succ q')) y ≐ zero)) :
    Γ ⊢[PRAAx] lt (rank K (pairT zero (succ q')) y) (rank K (box B) y) ⋏
      (sel K (rank K (pairT zero (succ q')) y) (box B) y ≐ pairT zero (succ q')) :=
  scan_complete K (zero_le B)
    (le_congr (congrSucc (zero_root_den hB).eqSymm) (.eqRefl _) h1) hk

end LeanProofs.IPRA.Foundations.RationalRootScan
