import IPRADerivations.AnalyticNumberTheory.RobinLogName
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.AnalyticNumberTheory.ChebyshevAbel
import IPRADerivations.Core.Search
import IPRADerivations.Core.Header

/-!
# The logarithm interval `LogI(q, k)` with binary range reduction (`robin_ipra_research_2026-11-19`, §"Explicit interval arithmetic")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, §"A logarithm enclosure from a finite
geometric identity": "For an arbitrary positive rational `q ≥ 1`, bounded binary range reduction produces `q = 2^a y`, with
`a ≥ 0` and `1 ≤ y < 2`. The enclosure is the sum of `a` copies of the enclosure of `log 2` and the enclosure of `log y`.
… Taking `K = k + a + 4` … This defines a fixed primitive-recursive rational interval `LogI(q, k)` … Powers, denominators,
and the finite summation length are explicit."

For `q = a/b` with `1 ≤ b ≤ a`:

* `eb a b` is the exponent, a bounded search (`Search.mu`) for the least `e ≤ a` with `a < b 2^{e+1}`;
  `eb_spec`: `b 2^e ≤ a < b 2^{e+1}`; `exp_le`: the exponents are monotone in `q` (so `eb` is unique, `eb_eq`);
* with `B = b 2^e`, `y = a/B` has `z = (y − 1)/(y + 1) = d/s`, `d = a − B`, `s = a + B`, `s² = W + d²`, `W = 4Ba`
  (`st_sq`); `log 2 = log((1 + 1/3)/(1 − 1/3))` uses `p/s = 1/3`, `W = 8`;
* the lower end `lo(q, K) = e·S_K(1/3) + S_K(d/s) = loN/loD` and the upper end `hi(q, K) = e·U_K(1/3) + U_K(d/s) = hiN/hiD`
  (`RobinLogName`), with `LogI(q, k)` at `K = k + e + 4` (`Kp`);
* consistency and nesting: `lo_le_hi` (`lo ≤ hi`), `lo_nest`, `hi_nest` (`lo(K) ≤ lo(K + j)`, `hi(K + j) ≤ hi(K)`), and
  `lo_le_hi_any`: `lo(q, K) ≤ hi(q, K')` for all precisions `K, K'` — the intervals of one `q` are pairwise consistent;
* `lo_mono`, `lo_mono_le`, `logI_mono`: the lower end is monotone in `q` and in the precision. Within one binade this is
  the monotonicity of `S_K` in `z` (`RobinLogName.low_mono`); across binades `S_K(d/s) ≤ S_K(1/3)` because `y < 2`.

All statements are cleared cross-multiplications of natural-number terms. The identification of the names with the
real logarithm is the packet's external interpretation.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName
  (Nz Dz Un Ud Lz NF log_name low_up low_mono frac_trans Dz_pos Ud_pos Nz_congr Dz_congr Un_congr Ud_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (pw_exp_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw pw_pos')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Binary range reduction -/

/-- The search body over `0 = i`, `1 = ⟨a, b⟩`: zero iff `a < b 2^{i+1}`. -/
def ebB : PTm 2 := monus (succ (fstT (var 1))) (sndT (var 1) * pw two (succ (var 0)))

/-- The binary exponent of `a/b`: the least `e ≤ a` with `a < b 2^{e+1}`. -/
abbrev eb (a b : PTm n) : PTm n := Search.mu ebB (succ a) (pairT a b)

theorem eb_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 ebB i (pairT a b) ≐ monus (succ a) (b * pw two (succ i)) := by
  have e : inst2 ebB i (pairT a b) = monus (succ (fstT (pairT a b))) (sndT (pairT a b) * pw two (succ i)) := by
    simp [inst2, ebB]
  rw [e]
  exact congrMonus (congrSucc (fst_pair _ _)) (congrMul (snd_pair _ _) (.eqRefl _))

/-- `b 2^e ≤ a < b 2^{e+1}` for `1 ≤ b ≤ a`. -/
theorem eb_spec {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le (b * pw two (eb a b)) a ⋏ lt a (b * pw two (succ (eb a b))) := by
  have l1 := lt_pw (Γ := Γ) (p := two) (le_refl _) a
  have eP := natEq (pw_succ (Γ := Γ) two a)
  have hl : Γ ⊢[PRAAx] lt a (b * pw two (succ a)) := by
    ipra_le sl hb * 𝔞 (two * pw two a) + 𝔞 (pw two a) + sl l1 with 𝔞 b * eP
  have hf : Γ ⊢[PRAAx] inst2 ebB a (pairT a b) ≐ zero :=
    (eb_at a a b).eqTrans (show Γ ⊢[PRAAx] monus (succ a) (b * pw two (succ a)) ≐ zero from hl)
  have fd := Search.search_found (f := ebB) hf (le_refl (succ a) : Γ ⊢[PRAAx] lt a (succ a))
  have up : Γ ⊢[PRAAx] lt a (b * pw two (succ (eb a b))) :=
    (eb_at (eb a b) a b).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ fd))
  refine .andI ?_ up
  refine .orE (lt_or_le zero (eb a b)) ?_ ?_
  · let C : List (Fm PTm n) := lt zero (eb a b) :: Γ
    have ep : C ⊢[PRAAx] eb a b ≐ succ (pred (eb a b)) := pos_of_one_le Prf.hyp0
    have hm : C ⊢[PRAAx] lt (pred (eb a b)) (eb a b) := le_congr (.eqRefl _) ep.eqSymm (le_refl _)
    have nm := Search.search_minimal (f := ebB) hm
    refine .orE (lt_or_le a (b * pw two (eb a b))) ?_ Prf.hyp0
    have q : (lt a (b * pw two (eb a b)) :: C) ⊢[PRAAx] lt a (b * pw two (succ (pred (eb a b)))) :=
      lt_congr (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 powF ep.wk (.eqRefl _))) Prf.hyp0
    have c : (lt a (b * pw two (eb a b)) :: C) ⊢[PRAAx] inst2 ebB (pred (eb a b)) (pairT a b) ≐ zero :=
      (eb_at _ a b).eqTrans q
    exact .botE _ (.impE nm.wk c)
  · have e0 : (le (eb a b) zero :: Γ) ⊢[PRAAx] eb a b ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
    have p0 : (le (eb a b) zero :: Γ) ⊢[PRAAx] pw two (eb a b) ≐ one :=
      (congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)
    have x := natEq p0
    ipra_le sl hab.wk with -(𝔞 b) * x

/-- Exponents are monotone in `q`: from `b 2^e ≤ a`, `a' < b' 2^{c+1}` and `a/b ≤ a'/b'`, `e ≤ c`. -/
theorem exp_le {a b a' b' e c : PTm n} (hb : Γ ⊢[PRAAx] le one b)
    (h1 : Γ ⊢[PRAAx] le (b * pw two e) a) (h2 : Γ ⊢[PRAAx] lt a' (b' * pw two (succ c)))
    (hq : Γ ⊢[PRAAx] le (a * b') (a' * b)) : Γ ⊢[PRAAx] le e c := by
  refine .orE (lt_or_le c e) ?_ Prf.hyp0
  let C : List (Fm PTm n) := lt c e :: Γ
  have p : C ⊢[PRAAx] le (pw two (succ c)) (pw two e) := pw_exp_le Prf.hyp0
  have m1 := le_mul_mono p (le_refl (b * b'))
  have m2 := le_mul_mono (h1.wk : C ⊢[PRAAx] _) (le_refl b')
  have m3 := le_mul_mono (h2.wk : C ⊢[PRAAx] le (succ a') (b' * pw two (succ c))) (le_refl b)
  have hq' : C ⊢[PRAAx] le (a * b') (a' * b) := hq.wk
  have hb' : C ⊢[PRAAx] le one b := hb.wk
  exact lt_irrefl zero _ (by ipra_le sl m1 + sl m2 + sl hq' + sl m3 + sl hb')

/-- The exponent is the unique `c` with `b 2^c ≤ a < b 2^{c+1}`. -/
theorem eb_eq {a b c : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (h1 : Γ ⊢[PRAAx] le (b * pw two c) a) (h2 : Γ ⊢[PRAAx] lt a (b * pw two (succ c))) :
    Γ ⊢[PRAAx] eb a b ≐ c := by
  have s := eb_spec hb hab
  exact le_antisymm (exp_le hb (Prf.andE₁ s) h2 (le_refl _)) (exp_le hb h1 (Prf.andE₂ s) (le_refl _))

/-! ## The reduced argument -/

abbrev Bt (a b : PTm n) : PTm n := b * pw two (eb a b)
abbrev dt (a b : PTm n) : PTm n := monus a (Bt a b)
abbrev st (a b : PTm n) : PTm n := a + Bt a b
abbrev Wt (a b : PTm n) : PTm n := two * two * Bt a b * a
abbrev c3 : PTm n := succ two
abbrev c8 : PTm n := two * two * two

theorem a_eq {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] a ≐ Bt a b + dt a b := eq_add_of_le (Prf.andE₁ (eb_spec hb hab))

theorem st_sq {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] st a b * st a b ≐ Wt a b + dt a b * dt a b := by
  have e := natEq (a_eq hb hab)
  apply deriveNat; ipra_simps; rw [e]; ring

theorem one_le_Bt {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (Bt a b) := by
  have pp := natEq (pw_pos' (Γ := Γ) two_pos' (eb a b))
  ipra_le sl hb * 𝔞 (pw two (eb a b)) + 𝔞 (pred (pw two (eb a b))) with pp

theorem st_pos {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] st a b ≐ succ (pred (st a b)) :=
  pos_of_one_le (by ipra_le sl hb + sl hab + 𝔞 (Bt a b))

theorem Wt_pos {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] Wt a b ≐ succ (pred (Wt a b)) := by
  have m := le_mul_mono (one_le_Bt (a := a) hb) (le_trans hb hab)
  exact pos_of_one_le (by ipra_le sl m + 3 * 𝔞 (Bt a b * a))

theorem c3_pos : Γ ⊢[PRAAx] (c3 : PTm n) ≐ succ (pred c3) := pos_of_one_le (by ipra_le 2)
theorem c8_pos : Γ ⊢[PRAAx] (c8 : PTm n) ≐ succ (pred c8) := pos_of_one_le (by ipra_le 7)
theorem c3_sq : Γ ⊢[PRAAx] (c3 : PTm n) * c3 ≐ c8 + one * one := by ipra_ring

/-- `z = d/s ≤ 1/3`, since `y < 2`. -/
theorem z_third {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le (dt a b * c3) (one * st a b) := by
  have h2 := Prf.andE₂ (eb_spec hb hab)
  have hd := natEq (a_eq hb hab)
  have x := natEq (pw_succ (Γ := Γ) two (eb a b))
  ipra_le 2 * sl h2 + 2 with 3 * hd - 2 * 𝔞 b * x

/-! ## The two ends -/

/-- `lo(q, K) = e·S_K(1/3) + S_K(d/s)`. -/
abbrev loN (a b K : PTm n) : PTm n :=
  eb a b * Nz K one c3 * Dz K (dt a b) (st a b) + Nz K (dt a b) (st a b) * Dz K one c3
abbrev loD (a b K : PTm n) : PTm n := Dz K one c3 * Dz K (dt a b) (st a b)
/-- `hi(q, K) = e·U_K(1/3) + U_K(d/s)`. -/
abbrev hiN (a b K : PTm n) : PTm n :=
  eb a b * Un K one c3 c8 * Ud K (dt a b) (st a b) (Wt a b) + Un K (dt a b) (st a b) (Wt a b) * Ud K one c3 c8
abbrev hiD (a b K : PTm n) : PTm n := Ud K one c3 c8 * Ud K (dt a b) (st a b) (Wt a b)

/-- The precision of `LogI(q, k)`: `K = k + e + 4`. -/
abbrev Kp (a b k : PTm n) : PTm n := k + eb a b + succ (succ (succ (succ zero)))

theorem loN_congr (a b : PTm n) {K K' : PTm n} (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] loN a b K ≐ loN a b K' :=
  congrAdd (congrMul (congrMul (.eqRefl _) (Nz_congr _ _ e)) (Dz_congr _ _ e))
    (congrMul (Nz_congr _ _ e) (Dz_congr _ _ e))
theorem loD_congr (a b : PTm n) {K K' : PTm n} (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] loD a b K ≐ loD a b K' :=
  congrMul (Dz_congr _ _ e) (Dz_congr _ _ e)
theorem hiN_congr (a b : PTm n) {K K' : PTm n} (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] hiN a b K ≐ hiN a b K' :=
  congrAdd (congrMul (congrMul (.eqRefl _) (Un_congr _ _ _ e)) (Ud_congr _ _ _ e))
    (congrMul (Un_congr _ _ _ e) (Ud_congr _ _ _ e))
theorem hiD_congr (a b : PTm n) {K K' : PTm n} (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] hiD a b K ≐ hiD a b K' :=
  congrMul (Ud_congr _ _ _ e) (Ud_congr _ _ _ e)

theorem loD_pos {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K : PTm n) :
    Γ ⊢[PRAAx] loD a b K ≐ succ (pred (loD a b K)) :=
  Combinatorics.Binomial.pos_mul (Dz_pos c3_pos K one) (Dz_pos (st_pos hb hab) K _)

theorem hiD_pos {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K : PTm n) :
    Γ ⊢[PRAAx] hiD a b K ≐ succ (pred (hiD a b K)) :=
  Combinatorics.Binomial.pos_mul (Ud_pos c3_pos c8_pos K one) (Ud_pos (st_pos hb hab) (Wt_pos hb hab) K _)

/-- Two cleared inequalities `x_i/y_i ≤ c_i/d_i` give `e x_1/y_1 + x_2/y_2 ≤ e c_1/d_1 + c_2/d_2`. -/
theorem frac_sum (e : PTm n) {x1 y1 c1 d1 x2 y2 c2 d2 : PTm n} (h1 : Γ ⊢[PRAAx] le (x1 * d1) (c1 * y1))
    (h2 : Γ ⊢[PRAAx] le (x2 * d2) (c2 * y2)) :
    Γ ⊢[PRAAx] le ((e * x1 * y2 + x2 * y1) * (d1 * d2)) ((e * c1 * d2 + c2 * d1) * (y1 * y2)) := by
  ipra_le 𝔞 (e * y2 * d2) * sl h1 + 𝔞 (y1 * d1) * sl h2

/-! ## Consistency and nesting -/

/-- `lo(q, K) ≤ hi(q, K)`. -/
theorem lo_le_hi (a b K : PTm n) : Γ ⊢[PRAAx] le (loN a b K * hiD a b K) (hiN a b K * loD a b K) :=
  frac_sum (eb a b) (low_up K one c3 c8) (low_up K (dt a b) (st a b) (Wt a b))

/-- `lo(q, K) ≤ lo(q, K + j)` and `hi(q, K + j) ≤ hi(q, K)`. -/
theorem nest {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K j : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * loD a b (K + j)) (loN a b (K + j) * loD a b K) ⋏
      le (hiN a b (K + j) * hiD a b K) (hiN a b K * hiD a b (K + j)) := by
  have L3 := Prf.andE₁ (log_name (Γ := Γ) c3_pos c8_pos c3_sq K j)
  have Lt := Prf.andE₁ (log_name (Γ := Γ) (st_pos hb hab) (Wt_pos hb hab) (st_sq hb hab) K j)
  exact .andI (frac_sum (eb a b) (Prf.andE₁ L3) (Prf.andE₁ Lt)) (frac_sum (eb a b) (Prf.andE₂ L3) (Prf.andE₂ Lt))

theorem lo_nest {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) {K K' : PTm n}
    (hK : Γ ⊢[PRAAx] le K K') : Γ ⊢[PRAAx] le (loN a b K * loD a b K') (loN a b K' * loD a b K) := by
  have eK := (eq_add_of_le hK).eqSymm
  exact le_congr (congrMul (.eqRefl _) (loD_congr a b eK)) (congrMul (loN_congr a b eK) (.eqRefl _))
    (Prf.andE₁ (nest hb hab K (monus K' K)))

theorem hi_nest {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) {K K' : PTm n}
    (hK : Γ ⊢[PRAAx] le K K') : Γ ⊢[PRAAx] le (hiN a b K' * hiD a b K) (hiN a b K * hiD a b K') := by
  have eK := (eq_add_of_le hK).eqSymm
  exact le_congr (congrMul (hiN_congr a b eK) (.eqRefl _)) (congrMul (.eqRefl _) (hiD_congr a b eK))
    (Prf.andE₂ (nest hb hab K (monus K' K)))

/-- Consistency across precisions: `lo(q, K) ≤ hi(q, K')` for all `K, K'`. -/
theorem lo_le_hi_any {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (K K' : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * hiD a b K') (hiN a b K' * loD a b K) := by
  refine .orE (le_total K K') ?_ ?_
  · let C : List (Fm PTm n) := le K K' :: Γ
    have n1 := lo_nest (Γ := C) hb.wk hab.wk Prf.hyp0
    exact frac_trans (loD_pos hb.wk hab.wk K') n1 (lo_le_hi a b K')
  · let C : List (Fm PTm n) := le K' K :: Γ
    have n2 := hi_nest (Γ := C) hb.wk hab.wk Prf.hyp0
    exact frac_trans (hiD_pos hb.wk hab.wk K) (lo_le_hi a b K) n2

/-! ## Monotonicity of the lower end -/

/-- `lo(q, K) ≤ lo(q', K)` for `1 ≤ q = a/b ≤ q' = a'/b'`. -/
theorem lo_mono {a b a' b' : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hq : Γ ⊢[PRAAx] le (a * b') (a' * b)) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * loD a' b' K) (loN a' b' K * loD a b K) := by
  have s := eb_spec hb hab
  have s' := eb_spec hb' hab'
  have hee : Γ ⊢[PRAAx] le (eb a b) (eb a' b') := exp_le hb (Prf.andE₁ s) (Prf.andE₂ s') hq
  refine .orE (lt_or_eq_of_le hee) ?_ ?_
  · -- a lower binade: `lo(q) ≤ (e + 1) S_K(1/3) ≤ e' S_K(1/3) ≤ lo(q')`
    let C : List (Fm PTm n) := lt (eb a b) (eb a' b') :: Γ
    have hlt : C ⊢[PRAAx] lt (eb a b) (eb a' b') := Prf.hyp0
    have m := low_mono (z_third (Γ := C) hb.wk hab.wk) K
    ipra_le 𝔞 (Dz K one c3 * Dz K (dt a' b') (st a' b')) * sl m +
      𝔞 (Nz K one c3 * Dz K (dt a b) (st a b) * Dz K one c3 * Dz K (dt a' b') (st a' b')) * sl hlt +
      𝔞 (Nz K (dt a' b') (st a' b') * Dz K one c3 * Dz K one c3 * Dz K (dt a b) (st a b))
  · -- the same binade: `S_K` is monotone in `z`
    let C : List (Fm PTm n) := (eb a b ≐ eb a' b') :: Γ
    have ee : C ⊢[PRAAx] eb a b ≐ eb a' b' := Prf.hyp0
    have hd := natEq (a_eq (Γ := C) hb.wk hab.wk)
    have hd' := natEq (a_eq (Γ := C) hb'.wk hab'.wk)
    have pe := natEq (congrAp2 powF ee (.eqRefl (two : PTm n)))
    have eq := natEq ee
    have m0 := le_mul_mono (hq.wk : C ⊢[PRAAx] _) (le_refl (pw two (eb a b)))
    have hz : C ⊢[PRAAx] le (dt a b * st a' b') (dt a' b' * st a b) := by
      ipra_le 2 * sl m0 with (2 * 𝔞 (pw two (eb a b)) * 𝔞 b' + 𝔞 (dt a' b')) * hd -
        (2 * 𝔞 (pw two (eb a b)) * 𝔞 b + 𝔞 (dt a b)) * hd' +
        (2 * 𝔞 (pw two (eb a b)) * 𝔞 b * 𝔞 b' + 2 * 𝔞 b' * 𝔞 (dt a b)) * pe
    have lm := low_mono hz K
    ipra_le 𝔞 (Dz K one c3 * Dz K one c3) * sl lm with
      -(𝔞 (Nz K one c3) * 𝔞 (Lz K (dt a b) (st a b)) * 𝔞 (RobinGamma.Pv K (st a b)) * 𝔞 (Lz K (dt a' b') (st a' b')) * 𝔞 (RobinGamma.Pv K (st a' b')) * 𝔞 (Lz K one c3) * 𝔞 (RobinGamma.Pv K c3)) * eq

/-- `lo(q, K) ≤ lo(q', K')` for `q ≤ q'` and `K ≤ K'`. -/
theorem lo_mono_le {a b a' b' K K' : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hq : Γ ⊢[PRAAx] le (a * b') (a' * b))
    (hK : Γ ⊢[PRAAx] le K K') :
    Γ ⊢[PRAAx] le (loN a b K * loD a' b' K') (loN a' b' K' * loD a b K) :=
  frac_trans (loD_pos hb hab K') (lo_nest hb hab hK) (lo_mono hb hab hb' hab' hq K')

/-- `LogI`: the lower end at `K = k + e + 4` is monotone in `q` and in the precision `k`. -/
theorem logI_mono {a b a' b' k k' : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hq : Γ ⊢[PRAAx] le (a * b') (a' * b))
    (hk : Γ ⊢[PRAAx] le k k') :
    Γ ⊢[PRAAx] le (loN a b (Kp a b k) * loD a' b' (Kp a' b' k')) (loN a' b' (Kp a' b' k') * loD a b (Kp a b k)) := by
  have hee := exp_le hb (Prf.andE₁ (eb_spec hb hab)) (Prf.andE₂ (eb_spec hb' hab')) hq
  exact lo_mono_le hb hab hb' hab' hq (by ipra_le sl hk + sl hee)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
