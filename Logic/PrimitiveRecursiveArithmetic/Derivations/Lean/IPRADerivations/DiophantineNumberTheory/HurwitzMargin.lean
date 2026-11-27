import IPRADerivations.DiophantineNumberTheory.HurwitzDenominator

/-!
# The margin certificate of the sharp Hurwitz theorem (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, "A rational replacement
for the three-convergent argument" and "An entirely finite certificate interface": for the pair
`(u, v)` selected by the denominator lemma, with `C = uv/(u² + v²)` and `d = 1 − 5C² > 0`, the
smaller weighted error is at most `C`, and an enclosure of half-width `e` with `Q² e ≤ d/100` gives
the strict certificate `5 q⁴ (|y − p/q| + e)² < 1` for the selected `p/q`.

All quantities are cleared of denominators. With a common denominator `W` for the rational errors
(`a = W |y − r/u|`, `b = W |y − t/v|`, the bracket `|y − r/u| + |y − t/v| = 1/(uv)` reading
`uv (a + b) = W`), `S = u² + v²`, `D = S² − 5u²v²` (so `d = D/S²`) and an enclosure numerator `E`
(`e = E/W`):

* `min_weight`: `u²a ≤ v²b` gives `u²a · S ≤ uv W` (the smaller weighted error is `≤ C`);
* `margin_core`: `100 S² X ≤ (100 uv S + D) W` with `D, W ≥ 1` gives `5X² < W²`, by
  `10000 S⁴ − 5(100uvS + D)² = 5D (1899 S² + 100 S k + 5u²v²)`, `S = 2uv + k`;
* `certificate` (closed sentence): under `5u²v² < S²` (`goodPair`), `uv(a + b) = W ≥ 1`,
  `u, v ≤ Q` and `100 S² Q² E ≤ D W`, the selected fraction satisfies the certificate:
  `u²a ≤ v²b → 5 (u²(a + E))² < W²` and `v²b ≤ u²a → 5 (v²(b + E))² < W²`, which is
  `5 q⁴ (|y − p/q| + e)² < 1`.

The selection of the pair (`HurwitzDenominator.denominator_lemma`) and this certificate are the
integer core of the finite certificate interface; the enclosure of a rational name in the
convergent brackets and the extraction of the continued-fraction prefix are not derived.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzMargin

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzDenominator (goodPair)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `2uv ≤ u² + v²`. -/
theorem two_uv_le (u v : PTm n) : Γ ⊢[PRAAx] le (two * u * v) (u * u + v * v) := by
  refine .orE (le_total u v) ?_ ?_
  · refine le_of_eq_add (d := monus v u * monus v u) ?_
    have e := natEq (eq_add_of_le (Γ := le u v :: Γ) Prf.hyp0)
    apply deriveNat; ipra_simps
    have ev : 𝔞 v = 𝔞 u + 𝔞 (monus v u) := e
    rw [ev]; ring
  · refine le_of_eq_add (d := monus u v * monus u v) ?_
    have e := natEq (eq_add_of_le (Γ := le v u :: Γ) Prf.hyp0)
    apply deriveNat; ipra_simps
    have eu : 𝔞 u = 𝔞 v + 𝔞 (monus u v) := e
    rw [eu]; ring

/-- The smaller weighted error is at most `C = uv/S`: `u²a ≤ v²b` and `uv(a + b) = W` give
`u²a S ≤ uv W`. -/
theorem min_weight {u v a b W : PTm n} (hW : Γ ⊢[PRAAx] u * v * (a + b) ≐ W)
    (h : Γ ⊢[PRAAx] le (u * u * a) (v * v * b)) :
    Γ ⊢[PRAAx] le (u * u * a * (u * u + v * v)) (u * v * W) := by
  refine le_of_eq_add (d := u * u * monus (v * v * b) (u * u * a)) ?_
  ipra_lc 𝔞 u * 𝔞 u * natEq (eq_add_of_le h) - 𝔞 u * 𝔞 v * natEq hW

/-- The margin: `100 S² X ≤ (100 uv S + D) W` with `S² = 5u²v² + D`, `D, W ≥ 1` gives `5X² < W²`. -/
theorem margin_core {u v D X W : PTm n}
    (hD : Γ ⊢[PRAAx] (u * u + v * v) * (u * u + v * v) ≐ num 5 * (u * u) * (v * v) + D)
    (hD1 : Γ ⊢[PRAAx] le one D) (hW1 : Γ ⊢[PRAAx] le one W)
    (h : Γ ⊢[PRAAx] le (num 100 * ((u * u + v * v) * (u * u + v * v)) * X)
      ((num 100 * u * v * (u * u + v * v) + D) * W)) :
    Γ ⊢[PRAAx] lt (num 5 * X * X) (W * W) := by
  refine .orE (lt_or_le (num 5 * X * X) (W * W)) Prf.hyp0 ?_
  let Δ : List (Fm PTm n) := le (W * W) (num 5 * X * X) :: Γ
  let S : PTm n := u * u + v * v
  let k : PTm n := monus S (two * u * v)
  let g : PTm n := monus ((num 100 * u * v * S + D) * W) (num 100 * (S * S) * X)
  let w : PTm n := monus (num 5 * X * X) (W * W)
  let D0 : PTm n := monus D one
  let W0 : PTm n := monus W one
  let DW1 : PTm n := D0 * (succ W0 * succ W0) + two * W0 + W0 * W0
  let P1 : PTm n := num 1899 * (num 5 * (u * u) * (v * v) + D0) + num 100 * S * k + num 5 * (u * u) * (v * v)
  refine .botE _ (succ_ne_zero (a := num 9494 + num 9495 * DW1 + num 5 * (DW1 + one) * P1 +
    num 10000 * (S * S) * (S * S) * w + num 10 * (num 100 * (S * S) * X) * g + num 5 * g * g) ?_)
  have e1 := natEq (eq_add_of_le (Γ := Δ) h.wk)
  have e2 := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
  have ek := natEq (eq_add_of_le (Γ := Δ) (two_uv_le u v))
  have eD := natEq (Γ := Δ) hD.wk
  have eD0 := natEq (eq_add_of_le (Γ := Δ) hD1.wk)
  have eW0 := natEq (eq_add_of_le (Γ := Δ) hW1.wk)
  apply deriveNat; simp only [S, k, g, w, D0, W0, DW1, P1] at *; ipra_simps; push_cast at *
  have sg : (𝔞 (monus ((num 100 * u * v * (u * u + v * v) + D) * W) (num 100 * ((u * u + v * v) * (u * u + v * v)) * X)) : Groth (Q Δ)) =
      (100 * 𝔞 u * 𝔞 v * (𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v) + 𝔞 D) * 𝔞 W -
        100 * ((𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v) * (𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v)) * 𝔞 X := by
    linear_combination -e1
  have sw : (𝔞 (monus (num 5 * X * X) (W * W)) : Groth (Q Δ)) = 5 * 𝔞 X * 𝔞 X - 𝔞 W * 𝔞 W := by linear_combination -e2
  have sk : (𝔞 (monus (u * u + v * v) (two * u * v)) : Groth (Q Δ)) = 𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v - 2 * 𝔞 u * 𝔞 v := by
    linear_combination -ek
  have sD0 : (𝔞 (monus D one) : Groth (Q Δ)) = 𝔞 D - 1 := by linear_combination -eD0
  have sW0 : (𝔞 (monus W one) : Groth (Q Δ)) = 𝔞 W - 1 := by linear_combination -eW0
  have sD : (𝔞 D : Groth (Q Δ)) = (𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v) * (𝔞 u * 𝔞 u + 𝔞 v * 𝔞 v) - 5 * (𝔞 u * 𝔞 u) * (𝔞 v * 𝔞 v) := by
    linear_combination -eD
  rw [sg, sw, sk, sD0, sW0, sD]
  ring

theorem le_mul_mono {Γ : List (Fm PTm n)} {a b : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (c * a) (c * b) := by
  refine le_of_eq_add (d := c * monus b a) ?_
  ipra_lc 𝔞 c * natEq (eq_add_of_le h)

theorem sq_le_sq {Γ : List (Fm PTm n)} {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (a * a) (b * b) := by
  refine le_of_eq_add (d := two * a * monus b a + monus b a * monus b a) ?_
  have e := natEq (eq_add_of_le h)
  apply deriveNat; ipra_simps
  have eb : 𝔞 b = 𝔞 a + 𝔞 (monus b a) := e
  rw [eb]; ring

theorem add_le_add' {Γ : List (Fm PTm n)} {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a + c) (b + d) := by
  refine le_of_eq_add (d := monus b a + monus d c) ?_
  ipra_lc natEq (eq_add_of_le h₁) + natEq (eq_add_of_le h₂)

/-- The certificate for the selected fraction `r/u` (with error numerator `a`). -/
theorem cert_one {u v a b E W Q D : PTm n} (hW : Γ ⊢[PRAAx] u * v * (a + b) ≐ W) (hW1 : Γ ⊢[PRAAx] le one W)
    (hD : Γ ⊢[PRAAx] (u * u + v * v) * (u * u + v * v) ≐ num 5 * (u * u) * (v * v) + D)
    (hD1 : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le u Q)
    (hE : Γ ⊢[PRAAx] le (num 100 * ((u * u + v * v) * (u * u + v * v)) * (Q * Q) * E) (D * W))
    (hsel : Γ ⊢[PRAAx] le (u * u * a) (v * v * b)) :
    Γ ⊢[PRAAx] lt (num 5 * (u * u * (a + E)) * (u * u * (a + E))) (W * W) := by
  refine margin_core hD hD1 hW1 ?_
  -- `100 S² u² a ≤ 100 S uv W` and `100 S² u² E ≤ 100 S² Q² E ≤ D W`
  have h1 := le_mul_mono (num 100 * (u * u + v * v)) (min_weight hW hsel)
  have h2 := le_mul_mono (num 100 * ((u * u + v * v) * (u * u + v * v)) * E) (sq_le_sq hQ)
  have h2' := le_trans h2 (le_congr (by ipra_ring) (.eqRefl _) hE)
  have hs := add_le_add' h1 h2'
  exact le_congr (by ipra_ring) (by ipra_ring) hs

/-- The certificate for both selections, from the hypotheses in a context. -/
theorem cert_core {u v a b E W Q : PTm n} (hgood : Γ ⊢[PRAAx] goodPair u v)
    (hW : Γ ⊢[PRAAx] u * v * (a + b) ≐ W) (hW1 : Γ ⊢[PRAAx] le one W) (hQu : Γ ⊢[PRAAx] le u Q)
    (hQv : Γ ⊢[PRAAx] le v Q)
    (hE : Γ ⊢[PRAAx] le (num 100 * ((u * u + v * v) * (u * u + v * v)) * (Q * Q) * E)
      (monus ((u * u + v * v) * (u * u + v * v)) (num 5 * (u * u) * (v * v)) * W)) :
    Γ ⊢[PRAAx] (le (u * u * a) (v * v * b) ⟶
        lt (num 5 * (u * u * (a + E)) * (u * u * (a + E))) (W * W)) ⋏
      (le (v * v * b) (u * u * a) ⟶ lt (num 5 * (v * v * (b + E)) * (v * v * (b + E))) (W * W)) := by
  let D : PTm n := monus ((u * u + v * v) * (u * u + v * v)) (num 5 * (u * u) * (v * v))
  have hD : Γ ⊢[PRAAx] (u * u + v * v) * (u * u + v * v) ≐ num 5 * (u * u) * (v * v) + D :=
    eq_add_of_le (le_of_lt hgood)
  have hD1 : Γ ⊢[PRAAx] le one D := by
    have e := natEq (eq_add_of_le hgood)
    have e' := natEq hD
    refine le_of_eq_add (d := monus ((u * u + v * v) * (u * u + v * v)) (succ (num 5 * (u * u) * (v * v)))) ?_
    ipra_lc [D] e - e'
  refine .andI (.impI ?_) (.impI ?_)
  · exact cert_one hW.wk hW1.wk hD.wk hD1.wk hQu.wk hE.wk Prf.hyp0
  · have hW' : Γ ⊢[PRAAx] v * u * (b + a) ≐ W := (by ipra_ring : Γ ⊢[PRAAx] v * u * (b + a) ≐ u * v * (a + b)).eqTrans hW
    have hD' : Γ ⊢[PRAAx] (v * v + u * u) * (v * v + u * u) ≐ num 5 * (v * v) * (u * u) + D := by
      ipra_lc natEq hD
    have hE' : Γ ⊢[PRAAx] le (num 100 * ((v * v + u * u) * (v * v + u * u)) * (Q * Q) * E) (D * W) :=
      le_congr (by ipra_ring) (.eqRefl _) hE
    exact cert_one hW'.wk hW1.wk hD'.wk hD1.wk hQv.wk hE'.wk Prf.hyp0

/-- Variables `0 = u`, `1 = v`, `2 = a`, `3 = b`, `4 = E`, `5 = W`, `6 = Q`. -/
def certFormula : Fm PTm 7 :=
  goodPair (var 0) (var 1) ⟶
    ((var 0 * var 1 * (var 2 + var 3) ≐ var 5) ⟶ (le one (var 5) ⟶ (le (var 0) (var 6) ⟶ (le (var 1) (var 6) ⟶
      (le (num 100 * ((var 0 * var 0 + var 1 * var 1) * (var 0 * var 0 + var 1 * var 1)) * (var 6 * var 6) * var 4)
          (monus ((var 0 * var 0 + var 1 * var 1) * (var 0 * var 0 + var 1 * var 1))
            (num 5 * (var 0 * var 0) * (var 1 * var 1)) * var 5) ⟶
        ((le (var 0 * var 0 * var 2) (var 1 * var 1 * var 3) ⟶
            lt (num 5 * (var 0 * var 0 * (var 2 + var 4)) * (var 0 * var 0 * (var 2 + var 4))) (var 5 * var 5)) ⋏
          (le (var 1 * var 1 * var 3) (var 0 * var 0 * var 2) ⟶
            lt (num 5 * (var 1 * var 1 * (var 3 + var 4)) * (var 1 * var 1 * (var 3 + var 4))) (var 5 * var 5))))))))

/-- The Hurwitz margin certificate, as a closed sentence of iPRA. -/
theorem certificate : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 certFormula :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (cert_core (u := var 0) (v := var 1) (a := var 2) (b := var 3) (E := var 4) (W := var 5) (Q := var 6)
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp)))))))))

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzMargin
