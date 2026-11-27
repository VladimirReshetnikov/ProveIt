import IPRADerivations.Core.Parity
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# The denominator lemma of the sharp Hurwitz theorem (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, "Denominator lemma":
"Let `1 ≤ u ≤ v`, `w ≥ u + v`, and `gcd(u, v) = 1`. At least one of the two rational numbers
`S₀ = (u² + v²)/(uv)`, `S₁ = (v² + w²)/(vw)` has square strictly greater than `5`. A suitable one is
selected by an integer comparison." This is the step that keeps the sharp constant `1/√5` without
comparing reals.

Here `S² > 5` is cleared of denominators, `goodPair u v :≡ 5u²v² < (u² + v²)²`, and coprimality is
supplied as it arises for consecutive convergents, by the determinant `r v − t u = ±1`
(`DiophantineNumberTheory/Recurrences.det_sq`):

* `good_of_gap`: `v² = uv + u² + 1 + e` gives `goodPair u v`, by the factorization
  `(u² + v²)² − 5u²v² = h (h + 2uv)` with `h = v² − uv − u²`;
* `unit_of_mul`: `u X = u Y + 1` forces `u = 1`;
* `no_golden_unit`: `v² = v + 1` has no natural solution;
* `denominator_lemma` (closed sentence): for all `u, v, w, r, t` with `u + v ≤ w` and
  `r v = t u + 1` or `t u = r v + 1`, `goodPair u v ∨ goodPair v w`. The selection is the integer
  comparison of `v²` with `uv + u²`: `h > 0` selects `S₀`, `h < 0` selects `S₁` (since
  `w² − vw − v² = −h + f(f + 2u + v) > 0` for `w = u + v + f`), and `h = 0` is impossible because
  the determinant makes `u` divide `1` and then `v² = v + 1`.

The hypotheses `1 ≤ u ≤ v` of the packet are not needed for the conclusion.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzDenominator

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `S² > 5` for `S = (u² + v²)/(uv)`, cleared: `5u²v² < (u² + v²)²`. -/
def goodPair (u v : PTm n) : Fm PTm n := lt (num 5 * (u * u) * (v * v)) ((u * u + v * v) * (u * u + v * v))

ipra_subst goodPair

/-- `h = v² − uv − u² = 1 + e > 0` gives `S₀² > 5`. -/
theorem good_of_gap {u v e : PTm n} (h : Γ ⊢[PRAAx] v * v ≐ u * v + u * u + succ e) : Γ ⊢[PRAAx] goodPair u v := by
  refine le_of_eq_add (d := e + two * u * v * succ e + e * succ e) ?_
  ipra_lc (𝔞 v * 𝔞 v + 𝔞 u * 𝔞 v - 𝔞 u * 𝔞 u + 1 + 𝔞 e) * natEq h

/-- `u X = u Y + 1` forces `u = 1`. -/
theorem unit_of_mul {u X Y : PTm n} (h : Γ ⊢[PRAAx] u * X ≐ u * Y + one) : Γ ⊢[PRAAx] u ≐ one := by
  refine .orE (lt_or_le Y X) ?_ ?_
  · -- `X = Y + 1 + g`, so `u + u g = 1`
    let Δ : List (Fm PTm n) := lt Y X :: Γ
    have eh := natEq (Γ := Δ) h.wk
    have hsum : Δ ⊢[PRAAx] u + u * monus X (succ Y) ≐ one := by
      ipra_lc eh - 𝔞 u * natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    refine .orE (zero_or_succ u) ?_ ?_
    · refine .botE _ (succ_ne_zero (a := zero) ?_)
      have e0 := natEq (Prf.hyp0 (Γ := Δ) (φ := u ≐ zero))
      ipra_lc -natEq hsum.wk (Γ := (u ≐ zero) :: Δ) + (1 + 𝔞 (monus X (succ Y))) * e0
    · have es := natEq hsum.wk (Γ := (u ≐ succ (pred u)) :: Δ)
      have hz : ((u ≐ succ (pred u)) :: Δ) ⊢[PRAAx] pred u + u * monus X (succ Y) ≐ zero := by
        ipra_lc es - natEq (Prf.hyp0 (φ := u ≐ succ (pred u)))
      exact Prf.hyp0.eqTrans (congrSucc (add_eq_zero_left hz))
  · -- `Y = X + g`, so `0 = u g + 1`
    refine .botE _ (succ_ne_zero (a := u * monus Y X) ?_)
    have eY := natEq (eq_add_of_le (Γ := le X Y :: Γ) Prf.hyp0)
    ipra_lc -natEq (Γ := le X Y :: Γ) h.wk - 𝔞 u * eY

/-- `v² = v + 1` has no natural solution. -/
theorem no_golden_unit {v : PTm n} (h : Γ ⊢[PRAAx] v * v ≐ v + one) : Γ ⊢[PRAAx] Fm.bot := by
  refine .orE (zero_or_succ v) ?_ ?_
  · refine succ_ne_zero (a := zero) ?_
    have e := natEq h.wk (Γ := (v ≐ zero) :: Γ)
    ipra_lc -e + (𝔞 v - 1) * natEq (Prf.hyp0 (φ := v ≐ zero))
  · let Δ : List (Fm PTm n) := (v ≐ succ (pred v)) :: Γ
    refine .orE (zero_or_succ (pred v)) ?_ ?_
    · refine succ_ne_zero (a := zero) ?_
      have e := natEq h.wk.wk (Γ := (pred v ≐ zero) :: Δ)
      have e1 := natEq (show ((pred v ≐ zero) :: Δ) ⊢[PRAAx] v ≐ succ (pred v) from Prf.hyp1)
      ipra_lc -e + 𝔞 v * e1 + 𝔞 v * natEq (Prf.hyp0 (φ := pred v ≐ zero))
    · refine succ_ne_zero (a := pred (pred v) * pred (pred v) + num 3 * pred (pred v)) ?_
      have e := natEq h.wk.wk (Γ := (pred v ≐ succ (pred (pred v))) :: Δ)
      have e1 := natEq (show ((pred v ≐ succ (pred (pred v))) :: Δ) ⊢[PRAAx] v ≐ succ (pred v) from Prf.hyp1)
      ipra_lc e - (𝔞 v + 𝔞 (pred (pred v)) + 1) * (e1 + natEq (Prf.hyp0 (φ := pred v ≐ succ (pred (pred v)))))

/-- The denominator lemma: `u + v ≤ w` and the determinant `r v − t u = ±1` give
`goodPair u v ∨ goodPair v w`, the choice made by comparing `v²` with `uv + u²`. -/
theorem denominator_core {u v w r t : PTm n} (hw : Γ ⊢[PRAAx] le (u + v) w)
    (hdet : Γ ⊢[PRAAx] (r * v ≐ t * u + one) ⋎ (t * u ≐ r * v + one)) :
    Γ ⊢[PRAAx] goodPair u v ⋎ goodPair v w := by
  refine .orE (lt_or_le (u * v + u * u) (v * v)) ?_ ?_
  · -- `h > 0`: choose `S₀`
    refine .orI₁ (good_of_gap (e := monus (v * v) (succ (u * v + u * u))) ?_)
    ipra_lc natEq (eq_add_of_le (Γ := lt (u * v + u * u) (v * v) :: Γ) Prf.hyp0)
  · let Δ : List (Fm PTm n) := le (v * v) (u * v + u * u) :: Γ
    refine .orE (lt_or_le (v * v) (u * v + u * u)) ?_ ?_
    · -- `h < 0`: choose `S₁`
      let Δ' : List (Fm PTm n) := lt (v * v) (u * v + u * u) :: Δ
      let f : PTm n := monus w (u + v)
      let e' : PTm n := monus (u * v + u * u) (succ (v * v))
      refine .orI₂ (good_of_gap (u := v) (v := w) (e := e' + f * (f + two * u + v)) ?_)
      ipra_lc (𝔞 w + 𝔞 u + 𝔞 f) * natEq (eq_add_of_le (Γ := Δ') hw.wk.wk) + natEq (eq_add_of_le (Γ := Δ') Prf.hyp0)
    · -- `h = 0` is impossible
      let Δ' : List (Fm PTm n) := le (u * v + u * u) (v * v) :: Δ
      have heq : Δ' ⊢[PRAAx] v * v ≐ u * v + u * u := le_antisymm Prf.hyp1 Prf.hyp0
      refine .botE _ ?_
      have hu : Δ' ⊢[PRAAx] u ≐ one := by
        refine .orE hdet.wk.wk ?_ ?_
        · refine unit_of_mul (X := r * r * (u + v)) (Y := t * t * u + two * t) ?_
          have eq' := natEq heq.wk (Γ := (r * v ≐ t * u + one) :: Δ')
          have hd := natEq (Prf.hyp0 (Γ := Δ') (φ := r * v ≐ t * u + one))
          ipra_lc -(𝔞 r * 𝔞 r) * eq' + (𝔞 r * 𝔞 v + 𝔞 t * 𝔞 u + 1) * hd
        · refine unit_of_mul (X := r * r * (u + v) + two * t) (Y := t * t * u) ?_
          have eq' := natEq heq.wk (Γ := (t * u ≐ r * v + one) :: Δ')
          have hd := natEq (Prf.hyp0 (Γ := Δ') (φ := t * u ≐ r * v + one))
          ipra_lc -(𝔞 r * 𝔞 r) * eq' + (1 - 𝔞 t * 𝔞 u - 𝔞 r * 𝔞 v) * hd
      refine no_golden_unit (v := v) ?_
      ipra_lc natEq heq + (𝔞 v + 𝔞 u + 1) * natEq hu

/-- Variables `0 = u`, `1 = v`, `2 = w`, `3 = r`, `4 = t`. -/
def denominatorFormula : Fm PTm 5 :=
  le (var 0 + var 1) (var 2) ⟶
    (((var 3 * var 1 ≐ var 4 * var 0 + one) ⋎ (var 4 * var 0 ≐ var 3 * var 1 + one)) ⟶
      (goodPair (var 0) (var 1) ⋎ goodPair (var 1) (var 2)))

/-- The denominator lemma of the sharp Hurwitz theorem, as a closed sentence of iPRA. -/
theorem denominator_lemma : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 denominatorFormula :=
  closeUniv 5 (.impI (.impI (denominator_core Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzDenominator
