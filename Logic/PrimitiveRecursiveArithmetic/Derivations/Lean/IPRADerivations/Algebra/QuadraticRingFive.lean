import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# The norm of `ℤ[√−5]`: zero, units, and the absence of norms `2` and `3`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/algebraic.tex`, Theorems `ag:norm`
and `ag:nonufd`, in the ring `R = ℤ[θ]`, `θ² = −5`, with the norm `N(a + bθ) = a² + 5b²`.

The norm depends only on the absolute values of the coordinates, so the statements about norm values are
statements about natural numbers `a`, `b`. Multiplicativity of the norm is `QuadraticExtension.norm_mul`.

* `norm_zero` (`ag:norm`): `a² + 5b² = 0` gives `a = 0` and `b = 0`;
* `unit_norm` (`ag:norm`): `a² + 5b² = 1` gives `a = 1` and `b = 0` (the units are `±1`);
* `integrality_re`, `integrality_im` (`ag:norm`): the two coordinates of
  `u² − 2a u + (a² + 5b²) = 0` for `u = a + bθ`, with the negative terms on the right;
* **`no_norm_two`**, **`no_norm_three`** (`ag:nonufd`): no element has norm `2` or `3`;
* `six_two_ways` (`ag:nonufd`): `2 · 3 = 6 = 1² + 5 · 1²`, the norm of `1 ± θ` and the value of
  `(1 + θ)(1 − θ)`.

The deduction of irreducibility from the absence of these norms (the case analysis of the factorizations of the
norms `4`, `9` and `6`) and the comparison of associates are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticRingFive

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The norm `a² + 5b²`. -/
abbrev N5 (a b : PTm n) : PTm n := a * a + num 5 * (b * b)

/-! ## The leaves of the case analysis -/

/-- `b ≥ 1` makes the norm at least `5`. -/
theorem big_b {a b p c e : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ p) (h : Γ ⊢[PRAAx] N5 a b ≐ c)
    (hc : Γ ⊢[PRAAx] c + succ e ≐ num 5) : Γ ⊢[PRAAx] Fm.bot := by
  have b1 := natEq hb; have h1 := natEq h; have c1 := natEq hc
  refine succ_ne_zero' _ (a := a * a + num 5 * (p * p) + num 10 * p + e) ?_
  ipra_lc h1 - 5 * (𝔞 b + 𝔞 p + 1) * b1 + c1

/-- `a = 0`, `b = 0` and a positive norm are incompatible. -/
theorem zero_zero {a b e : PTm n} (ha : Γ ⊢[PRAAx] a ≐ zero) (hb : Γ ⊢[PRAAx] b ≐ zero)
    (h : Γ ⊢[PRAAx] N5 a b ≐ succ e) : Γ ⊢[PRAAx] Fm.bot := by
  have a1 := natEq ha; have b1 := natEq hb; have h1 := natEq h
  refine succ_ne_zero' _ (a := e) ?_
  ipra_lc -h1 + 𝔞 a * a1 + 5 * 𝔞 b * b1

/-- `a = 1`, `b = 0` and a norm `≥ 2` are incompatible. -/
theorem one_zero {a b p e : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ p) (hp : Γ ⊢[PRAAx] p ≐ zero)
    (hb : Γ ⊢[PRAAx] b ≐ zero) (h : Γ ⊢[PRAAx] N5 a b ≐ succ (succ e)) : Γ ⊢[PRAAx] Fm.bot := by
  have a1 := natEq ha; have p1 := natEq hp; have b1 := natEq hb; have h1 := natEq h
  refine succ_ne_zero' _ (a := e) ?_
  ipra_lc -h1 + (𝔞 a + 1) * (a1 + p1) + 5 * 𝔞 b * b1

/-- `a ≥ 2` makes the norm at least `4`. -/
theorem big_a {a b p r c e : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ p) (hp : Γ ⊢[PRAAx] p ≐ succ r)
    (h : Γ ⊢[PRAAx] N5 a b ≐ c) (hc : Γ ⊢[PRAAx] c + succ e ≐ num 4) : Γ ⊢[PRAAx] Fm.bot := by
  have a1 := natEq ha; have p1 := natEq hp; have h1 := natEq h; have c1 := natEq hc
  refine succ_ne_zero' _ (a := r * r + num 4 * r + num 5 * (b * b) + e) ?_
  ipra_lc h1 - (𝔞 a + 𝔞 r + 2) * (a1 + p1) + c1

/-! ## No element of norm `2` or `3` -/

/-- The case analysis for a norm value `c = succ (succ e₀)` with `c < 4`. -/
theorem no_small_norm {a b c e0 e4 e5 : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ (succ e0))
    (h4 : Γ ⊢[PRAAx] c + succ e4 ≐ num 4) (h5 : Γ ⊢[PRAAx] c + succ e5 ≐ num 5) :
    Γ ⊢[PRAAx] neg (N5 a b ≐ c) := by
  refine .impI ?_
  have h : ((N5 a b ≐ c) :: Γ) ⊢[PRAAx] N5 a b ≐ c := Prf.hyp0
  refine .orE (zero_or_succ b) ?_ ?_
  · have hb : ((b ≐ zero) :: (N5 a b ≐ c) :: Γ) ⊢[PRAAx] b ≐ zero := Prf.hyp0
    refine .orE (zero_or_succ a) ?_ ?_
    · have ha : ((a ≐ zero) :: (b ≐ zero) :: (N5 a b ≐ c) :: Γ) ⊢[PRAAx] a ≐ zero := Prf.hyp0
      exact zero_zero ha hb.wk (h.wk.wk.eqTrans hc.wk.wk.wk)
    · refine .orE (zero_or_succ (pred a)) ?_ ?_
      · let C : List (Fm PTm n) :=
          (pred a ≐ zero) :: (a ≐ succ (pred a)) :: (b ≐ zero) :: (N5 a b ≐ c) :: Γ
        have ha : C ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp1
        have hp : C ⊢[PRAAx] pred a ≐ zero := Prf.hyp0
        have hb' : C ⊢[PRAAx] b ≐ zero := hb.wk.wk
        have h' : C ⊢[PRAAx] N5 a b ≐ c := h.wk.wk.wk
        have hc' : C ⊢[PRAAx] c ≐ succ (succ e0) := hc.wk.wk.wk.wk
        exact one_zero ha hp hb' (h'.eqTrans hc')
      · let C : List (Fm PTm n) :=
          (pred a ≐ succ (pred (pred a))) :: (a ≐ succ (pred a)) :: (b ≐ zero) :: (N5 a b ≐ c) :: Γ
        have ha : C ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp1
        have hp : C ⊢[PRAAx] pred a ≐ succ (pred (pred a)) := Prf.hyp0
        have h' : C ⊢[PRAAx] N5 a b ≐ c := h.wk.wk.wk
        have h4' : C ⊢[PRAAx] c + succ e4 ≐ num 4 := h4.wk.wk.wk.wk
        exact big_a ha hp h' h4'
  · have hb : ((b ≐ succ (pred b)) :: (N5 a b ≐ c) :: Γ) ⊢[PRAAx] b ≐ succ (pred b) := Prf.hyp0
    exact big_b hb h.wk h5.wk.wk

theorem c2_4 : Γ ⊢[PRAAx] (two : PTm n) + succ one ≐ num 4 := by
  ipra_lc

theorem c2_5 : Γ ⊢[PRAAx] (two : PTm n) + succ two ≐ num 5 := by
  ipra_lc

theorem c3_4 : Γ ⊢[PRAAx] (succ two : PTm n) + succ zero ≐ num 4 := by
  ipra_lc

theorem c3_5 : Γ ⊢[PRAAx] (succ two : PTm n) + succ one ≐ num 5 := by
  ipra_lc

/-- **No element of norm `2`**. -/
theorem no_norm_two (a b : PTm n) : Γ ⊢[PRAAx] neg (N5 a b ≐ two) :=
  no_small_norm (e0 := zero) (.eqRefl _) c2_4 c2_5

/-- **No element of norm `3`**. -/
theorem no_norm_three (a b : PTm n) : Γ ⊢[PRAAx] neg (N5 a b ≐ succ two) :=
  no_small_norm (e0 := one) (.eqRefl _) c3_4 c3_5

/-! ## Norm zero and the units -/

theorem sq_zero_alg {a p X : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ p) (h : Γ ⊢[PRAAx] a * a + X ≐ zero) :
    Γ ⊢[PRAAx] Fm.bot := by
  have a1 := natEq ha; have h1 := natEq h
  refine succ_ne_zero' _ (a := p * p + two * p + X) ?_
  ipra_lc h1 - (𝔞 a + 𝔞 p + 1) * a1

theorem swap_alg {a b : PTm n} (h : Γ ⊢[PRAAx] N5 a b ≐ zero) :
    Γ ⊢[PRAAx] b * b + (a * a + num 4 * (b * b)) ≐ zero := by
  ipra_lc natEq h

/-- **The norm vanishes only at zero**. -/
theorem norm_zero {a b : PTm n} (h : Γ ⊢[PRAAx] N5 a b ≐ zero) : Γ ⊢[PRAAx] (a ≐ zero) ⋏ (b ≐ zero) := by
  refine .andI ?_ ?_
  · refine .orE (zero_or_succ a) Prf.hyp0 ?_
    exact .botE _ (sq_zero_alg (Prf.hyp0 (Γ := Γ) (φ := a ≐ succ (pred a))) h.wk)
  · refine .orE (zero_or_succ b) Prf.hyp0 ?_
    exact .botE _ (sq_zero_alg (Prf.hyp0 (Γ := Γ) (φ := b ≐ succ (pred b))) (swap_alg h).wk)

theorem one5 : Γ ⊢[PRAAx] (one : PTm n) + succ (succ two) ≐ num 5 := by
  ipra_lc

theorem unit_alg {a b p : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ p) (hb : Γ ⊢[PRAAx] b ≐ zero)
    (h : Γ ⊢[PRAAx] N5 a b ≐ one) : Γ ⊢[PRAAx] zero ≐ p + (p * p + p) := by
  ipra_lc -natEq h + (𝔞 a + 𝔞 p + 1) * natEq ha + 5 * 𝔞 b * natEq hb

/-- **The units**: `a² + 5b² = 1` gives `a = 1` and `b = 0`. -/
theorem unit_norm {a b : PTm n} (h : Γ ⊢[PRAAx] N5 a b ≐ one) : Γ ⊢[PRAAx] (a ≐ one) ⋏ (b ≐ zero) := by
  have hb : Γ ⊢[PRAAx] b ≐ zero := by
    refine .orE (zero_or_succ b) Prf.hyp0 ?_
    exact .botE _ (big_b (Prf.hyp0 (Γ := Γ) (φ := b ≐ succ (pred b))) h.wk one5)
  refine .andI ?_ hb
  refine .orE (zero_or_succ a) ?_ ?_
  · exact .botE _ (zero_zero (Prf.hyp0 (Γ := Γ) (φ := a ≐ zero)) hb.wk h.wk)
  · have ha : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    have pz : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] pred a ≐ zero :=
      (monus_zero (pred a)).eqSymm.eqTrans (le_of_eq_add (unit_alg ha hb.wk h.wk))
    exact ha.eqTrans (congrSucc pz)

/-! ## Integrality and the two factorizations of `6` -/

/-- The first coordinate of `u² − 2a u + N(u) = 0`: `a² + (a² + 5b²) = 5b² + 2a²`. -/
theorem integrality_re (a b : PTm n) : Γ ⊢[PRAAx] a * a + N5 a b ≐ num 5 * (b * b) + two * (a * a) := by
  ipra_lc

/-- The second coordinate: `2ab = (2a) b`. -/
theorem integrality_im (a b : PTm n) : Γ ⊢[PRAAx] two * (a * b) ≐ (two * a) * b := by
  ipra_ring

/-- `2 · 3 = 6 = N(1 ± θ)`. -/
theorem six_two_ways : Γ ⊢[PRAAx] ((two : PTm n) * succ two ≐ num 6) ⋏ (N5 (one : PTm n) one ≐ num 6) := by
  refine .andI ?_ ?_
  · ipra_lc
  · ipra_lc

end LeanProofs.IPRA.Algebra.QuadraticRingFive
