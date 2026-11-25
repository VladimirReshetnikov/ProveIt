import IPRADerivations.DiophantineNumberTheory.SquareArea
import IPRADerivations.DiophantineNumberTheory.FermatQuartic
import IPRADerivations.Core.LinearCombination

/-!
# The rational points of the Fermat quartic

Packet: `diophantine-number-theory/faltings_ipra`, `sections/fermat_instance.tex`:

* `fourth_difference` (`lem:fq-difference`): no positive `x, y, z` with `x⁴ − y⁴ = z²`, by the
  square-area triangle `(2x²y², z², x⁴ + y⁴, xyz)` (`no_square_area`, the term form of
  `SquareArea.square_area`); and `a⁴ + b⁴ = c⁴` has no positive solution (`flt4'`, the term form of
  `FermatQuartic.flt4`);
* `quartic_points` (`thm:fq-complete`): for natural `x, y, z` (absolute values of the coordinates)
  with `x⁴ + y⁴ = z⁴`, one of `x, y` is `0` and the other equals `z`;
* `quartic_canonical`: for a primitive nonzero triple (no `d ≥ 2` divides all three), moreover
  `z = 1`, so the canonical points are `(1, 0, ±1)` and `(0, 1, ±1)`.

The other lemmas of the section are derived in the `mordell_weil_ipra` modules:
`lem:fq-gcd` (`Core/Bezout`, `Core/EuclidLemma`), `lem:fq-squares`
(`DiophantineNumberTheory/SquareSplit`), and `lem:fq-normalize`, `lem:fq-pyth`, `lem:fq-step`,
`thm:fq-no-area` (`DiophantineNumberTheory/SquareArea`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FermatQuarticPoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (q4)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (sq_inj dvd_self' one_le_of_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- No square-area triangle, at arbitrary terms. -/
theorem no_square_area {a b c s : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hE : Γ ⊢[PRAAx] a * a + b * b ≐ c * c)
    (hR : Γ ⊢[PRAAx] a * b ≐ two * (s * s)) : Γ ⊢[PRAAx] Fm.bot := by
  have h := inst (Γ := Γ) (Prf.allOpen (Prf.allOpen (Prf.allOpen (Prf.allOpen
    (SquareArea.square_area : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 SquareArea.squareAreaFormula)))))
    (![pred a, pred b, c, pred s] : Fin 4 → PTm n)
  simp at h
  refine Prf.impE h (.andI ?_ ?_)
  · exact (congrAdd (congrMul ha ha) (congrMul hb hb)).eqSymm.eqTrans hE
  · exact (congrMul ha hb).eqSymm.eqTrans (hR.eqTrans (congrMul (.eqRefl _) (congrMul hs hs)))

/-- `FLT(4)` at arbitrary terms: no positive `a, b` with `a⁴ + b⁴ = c⁴`. -/
theorem flt4' {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (h : Γ ⊢[PRAAx] q4 a + q4 b ≐ q4 c) : Γ ⊢[PRAAx] Fm.bot := by
  have i := inst (Γ := Γ) (Prf.allOpen (Prf.allOpen (Prf.allOpen
    (FermatQuartic.flt4 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 FermatQuartic.flt4Formula))))
    (![pred a, pred b, c] : Fin 3 → PTm n)
  simp at i
  refine Prf.impE i ?_
  have e₁ : Γ ⊢[PRAAx] q4 (succ (pred a)) ≐ q4 a := congrMul (congrMul ha ha) (congrMul ha ha) |>.eqSymm
  have e₂ : Γ ⊢[PRAAx] q4 (succ (pred b)) ≐ q4 b := congrMul (congrMul hb hb) (congrMul hb hb) |>.eqSymm
  exact (congrAdd e₁ e₂).eqTrans h

/-- `lem:fq-difference`: no positive `x, y, z` with `x⁴ − y⁴ = z²`, i.e. `y⁴ + z² = x⁴`. -/
theorem fourth_difference {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x))
    (hy : Γ ⊢[PRAAx] y ≐ succ (pred y)) (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (h : Γ ⊢[PRAAx] q4 y + z * z ≐ q4 x) : Γ ⊢[PRAAx] Fm.bot := by
  refine no_square_area (a := two * ((x * x) * (y * y))) (b := z * z) (c := q4 x + q4 y) (s := x * y * z)
    (pos_mul two_pos' (pos_mul (pos_mul hx hx) (pos_mul hy hy))) (pos_mul hz hz)
    (pos_mul (pos_mul hx hy) hz) ?_ ?_
  · ipra_lc (𝔞 z * 𝔞 z + 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x - 𝔞 y * 𝔞 y * 𝔞 y * 𝔞 y) * natEq h
  · ipra_ring

theorem q4_inj {u v : PTm n} (h : Γ ⊢[PRAAx] q4 u ≐ q4 v) : Γ ⊢[PRAAx] u ≐ v := sq_inj (sq_inj h)

theorem q4_zero {u : PTm n} (h : Γ ⊢[PRAAx] u ≐ zero) : Γ ⊢[PRAAx] q4 u ≐ zero :=
  (congrMul (congrMul h h) (congrMul h h)).eqTrans (by ipra_ring)

/-- `thm:fq-complete`, absolute values: `x⁴ + y⁴ = z⁴` forces a zero coordinate among `x, y`, and
then the other equals `z`. -/
theorem quartic_points {x y z : PTm n} (h : Γ ⊢[PRAAx] q4 x + q4 y ≐ q4 z) :
    Γ ⊢[PRAAx] ((x ≐ zero) ⋏ (y ≐ z)) ⋎ ((y ≐ zero) ⋏ (x ≐ z)) := by
  refine .orE (zero_or_succ x) ?_ ?_
  · have hx : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    exact .orI₁ (.andI hx (q4_inj ((zero_add _).eqSymm.eqTrans ((congrAdd (q4_zero hx).eqSymm (.eqRefl _)).eqTrans h.wk))))
  · refine .orE (zero_or_succ y) ?_ ?_
    · have hy : ((y ≐ zero) :: (x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      exact .orI₂ (.andI hy (q4_inj ((add_zero _).eqSymm.eqTrans ((congrAdd (.eqRefl _) (q4_zero hy).eqSymm).eqTrans h.wk.wk))))
    · exact .botE _ (flt4' Prf.hyp1 Prf.hyp0 h.wk.wk)

/-- Primitivity: no `d ≥ 2` divides `x`, `y` and `z`. -/
abbrev PrimF (x y z : PTm n) : Fm PTm n :=
  Fm.all (le two (var 0) ⟶ neg (dvd (var 0) (Syn.shift x) ⋏ (dvd (var 0) (Syn.shift y) ⋏ dvd (var 0) (Syn.shift z))))

/-- `thm:fq-complete`, canonical form: a primitive nonzero solution of `x⁴ + y⁴ = z⁴` has `z = 1` and
`(x, y) = (1, 0)` or `(0, 1)`. -/
theorem quartic_canonical {x y z : PTm n} (h : Γ ⊢[PRAAx] q4 x + q4 y ≐ q4 z)
    (hprim : Γ ⊢[PRAAx] PrimF x y z) (hnz : Γ ⊢[PRAAx] neg ((x ≐ zero) ⋏ ((y ≐ zero) ⋏ (z ≐ zero)))) :
    Γ ⊢[PRAAx] (z ≐ one) ⋏ (((x ≐ zero) ⋏ (y ≐ one)) ⋎ ((y ≐ zero) ⋏ (x ≐ one))) := by
  have hpI : ∀ (d : PTm n), Γ ⊢[PRAAx] le two d ⟶ neg (dvd d x ⋏ (dvd d y ⋏ dvd d z)) := fun d => by
    simpa using Prf.allE d hprim
  refine .orE (quartic_points h) ?_ ?_
  · let A : List (Fm PTm n) := ((x ≐ zero) ⋏ (y ≐ z)) :: Γ
    have hx : A ⊢[PRAAx] x ≐ zero := Prf.andE₁ Prf.hyp0
    have hyz : A ⊢[PRAAx] y ≐ z := Prf.andE₂ Prf.hyp0
    have hz : A ⊢[PRAAx] z ≐ succ (pred z) := by
      refine .orE (zero_or_succ z) ?_ Prf.hyp0
      have hz0 : ((z ≐ zero) :: A) ⊢[PRAAx] z ≐ zero := Prf.hyp0
      exact .botE _ (Prf.impE hnz.wk.wk (.andI hx.wk (.andI (hyz.wk.eqTrans hz0) hz0)))
    have z1 : A ⊢[PRAAx] z ≐ one := by
      refine .orE (lt_or_le one z) ?_ (le_antisymm Prf.hyp0 (one_le_of_pos hz.wk))
      have dx : (lt one z :: A) ⊢[PRAAx] dvd z x := (congrAp2 remF hx.wk (.eqRefl _)).eqTrans (rem_zero _)
      have dy : (lt one z :: A) ⊢[PRAAx] dvd z y := (congrAp2 remF hyz.wk (.eqRefl _)).eqTrans (dvd_self' hz.wk)
      exact .botE _ (Prf.impE (Prf.impE (hpI z).wk.wk Prf.hyp0) (.andI dx (.andI dy (dvd_self' hz.wk))))
    exact .andI z1 (.orI₁ (.andI hx (hyz.eqTrans z1)))
  · let B : List (Fm PTm n) := ((y ≐ zero) ⋏ (x ≐ z)) :: Γ
    have hy : B ⊢[PRAAx] y ≐ zero := Prf.andE₁ Prf.hyp0
    have hxz : B ⊢[PRAAx] x ≐ z := Prf.andE₂ Prf.hyp0
    have hz : B ⊢[PRAAx] z ≐ succ (pred z) := by
      refine .orE (zero_or_succ z) ?_ Prf.hyp0
      have hz0 : ((z ≐ zero) :: B) ⊢[PRAAx] z ≐ zero := Prf.hyp0
      exact .botE _ (Prf.impE hnz.wk.wk (.andI (hxz.wk.eqTrans hz0) (.andI hy.wk hz0)))
    have z1 : B ⊢[PRAAx] z ≐ one := by
      refine .orE (lt_or_le one z) ?_ (le_antisymm Prf.hyp0 (one_le_of_pos hz.wk))
      have dx : (lt one z :: B) ⊢[PRAAx] dvd z x := (congrAp2 remF hxz.wk (.eqRefl _)).eqTrans (dvd_self' hz.wk)
      have dy : (lt one z :: B) ⊢[PRAAx] dvd z y := (congrAp2 remF hy.wk (.eqRefl _)).eqTrans (rem_zero _)
      exact .botE _ (Prf.impE (Prf.impE (hpI z).wk.wk Prf.hyp0) (.andI dx (.andI dy (dvd_self' hz.wk))))
    exact .andI z1 (.orI₂ (.andI hy (hxz.eqTrans z1)))

end LeanProofs.IPRA.DiophantineNumberTheory.FermatQuarticPoints
