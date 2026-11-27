import IPRADerivations.DiophantineNumberTheory.KhinchinBadSum
import IPRADerivations.AnalyticNumberTheory.HarmonicUpper
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header
import IPRADerivations.Core.SumOrder

/-!
# The bad-pair estimate of (K3) (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, the proof of (K3):

  `Σ_{d=2}^Q A(⌊Q/d⌋) ≤ (λQ²/2) Σ_{d=2}^Q 1/d² + (λ/2 + 1) Q Σ_{d=2}^Q 1/d`,
  `Σ_{d=2}^Q 1/d² ≤ 3/4`, `Σ_{d=2}^{2^k} 1/d ≤ k`.                                        (K6)

With `J* = (α/β, γ/β)`, `D = γ − α` (so `λ = D/β`), `β = b₀ + 1`, `Q = 2^k ≥ 2` and numerators `p < M`
for `M ≥ Q`, the bad pairs `B(Q) = Σ_{q ≤ Q} #{p < M : p/q ∈ J*, gcd(p, q) ≠ 1}` satisfy

  `8β B(Q) + 4DQ ≤ 3DQ² + 4(D + 2β)(k + 1)Q`                                         (`bad_bound`)

i.e. `B(Q) ≤ 3λQ²/8 − λQ/2 + (λ/2 + 1)(k + 1)Q`. The steps:

* `KhinchinBadSum.bad_total`: `B(Q) ≤ Σ_{d ≤ Q} [2 ≤ d] A(⌊Q/d⌋)`;
* `per_d`, (K5) at `X = ⌊Q/d⌋ ≤ M`: `2β [2≤d] A(X) ≤ D [2≤d] X² + (D + 2β) [2≤d] X`, summed by the
  generic `sum_lin_le`;
* `sq_part`, the telescoping half of (K6) (`SquareReciprocal.square_bound`): `X² ≤ ⌊Q²/d²⌋`, and the
  terms `d = 0, 1` are removed, so `4 Σ [2≤d] X² + 4Q ≤ 3Q²`;
* `harm_part`, the dyadic half of (K6) (`HarmonicUpper.harmonic_upper`): `Σ [2≤d] ⌊Q/d⌋ ≤ (k + 1)Q`.

The harmonic sum keeps its term `d = 1` (the bound `(k + 1)Q` instead of `kQ`); the final (K7)
arithmetic has room for it.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadBound

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadSum (LB inst2_LB gate_zero bqB bad_total)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinLattice (aK latticeA lattice_core)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicUpper (harmonic_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (sqB T inst2_sq square_bound cancel_le)
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzMargin (le_mul_mono sq_le_sq add_le_add')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Summing a linear inequality -/

/-- Variables: `0 = N`, the rest shifted. -/
theorem sum_lin_le (f g h : PTm 2) (a b c x N : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f (var 0) (Syn.shift x))
        (Syn.shift b * inst2 g (var 0) (Syn.shift x) + Syn.shift c * inst2 h (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (a * ap2 (sumF f) N x) (b * ap2 (sumF g) N x + c * ap2 (sumF h) N x) := by
  exact sum_scaled_le_weighted_pair f g h a b c x x x N hp

/-! ## Gates -/

/-- `[2 ≤ d] ⌊Q/d⌋` in `(d, ⟨Q, y⟩)`. -/
abbrev P1 : PTm 2 := monus one (monus two (var 0)) * quo (fstT (var 1)) (var 0)

/-- `[2 ≤ d] ⌊Q/d⌋²` in `(d, ⟨Q, y⟩)`. -/
abbrev P2 : PTm 2 :=
  monus one (monus two (var 0)) * (quo (fstT (var 1)) (var 0) * quo (fstT (var 1)) (var 0))

theorem inst2_P1 (d z : PTm n) : inst2 P1 d z = monus one (monus two d) * quo (fstT z) d := by
  simp [inst2]

theorem inst2_P2 (d z : PTm n) :
    inst2 P2 d z = monus one (monus two d) * (quo (fstT z) d * quo (fstT z) d) := by
  simp [inst2]

/-- `(1 ∸ t) w ≤ w`. -/
theorem gate_le (t w : PTm n) : Γ ⊢[PRAAx] le (monus one t * w) w := by
  refine .orE (zero_or_succ t) ?_ ?_
  · have e : ((t ≐ zero) :: Γ) ⊢[PRAAx] monus one t * w ≐ w :=
      (congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)) (.eqRefl _)).eqTrans (one_mul _)
    exact le_congr e.eqSymm (.eqRefl _) (le_refl _)
  · have e : ((t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] monus one t * w ≐ zero :=
      (congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))
        (.eqRefl _)).eqTrans (zero_mul _)
    exact le_congr e.eqSymm (.eqRefl _) (zero_le _)

/-- `[2 ≤ 1] = 0`. -/
theorem gate_one : Γ ⊢[PRAAx] monus one (monus two (succ (zero : PTm n))) ≐ zero :=
  (congrMonus (.eqRefl _) ((succ_monus_succ _ _).eqTrans (monus_zero _))).eqTrans (monus_self _)

/-- `[2 ≤ j + 2] = 1`. -/
theorem gate_ss (j : PTm n) : Γ ⊢[PRAAx] monus one (monus two (succ (succ j))) ≐ one :=
  (congrMonus (.eqRefl _) ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))).eqTrans
    (monus_zero _)

/-- Shift a hypothesis under a bounded quantifier. -/
theorem shift_le {a b N : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have s := h.shift
  simp only [Fm.shift, subst_le] at s
  exact s.wk

theorem shift_eq {a b N : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := by
  have s := h.shift
  simp only [Fm.shift, Fm.subst_eq] at s
  exact s.wk

theorem shift_fst_eq {z Q N : PTm n} (h : Γ ⊢[PRAAx] fstT z ≐ Q) :
    (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] fstT (Syn.shift z) ≐ Syn.shift Q := by
  have s := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_fstT] at s
  exact s.wk

/-! ## (K5) for one divisor -/

/-- Cancelling `αX(X+1)` and multiplying by the gate, with atoms. -/
theorem k5_gate_aux {g A X α γ D β m : PTm n}
    (e : Γ ⊢[PRAAx] γ * (X * succ X) + two * β * X ≐ two * β * A + α * (X * succ X) + m)
    (eγ : Γ ⊢[PRAAx] γ ≐ α + D) :
    Γ ⊢[PRAAx] D * (g * (X * X)) + (D + two * β) * (g * X) ≐ two * β * (g * A) + g * m := by
  ipra_lc 𝔞 g * natEq e - 𝔞 g * (𝔞 X * 𝔞 X + 𝔞 X) * natEq eγ

/-- `2β [2≤d] A(⌊Q/d⌋) ≤ D [2≤d] ⌊Q/d⌋² + (D + 2β) [2≤d] ⌊Q/d⌋` for `Q ≤ M`. -/
theorem per_d {α γ b0 Q M : PTm n} (d : PTm n) (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hQM : Γ ⊢[PRAAx] le Q M) :
    Γ ⊢[PRAAx] le (two * succ b0 * inst2 LB d (pairT Q (pairT M (pairT α (pairT γ (succ b0))))))
      (monus γ α * inst2 P2 d (pairT Q (pairT M (pairT α (pairT γ (succ b0))))) +
        (monus γ α + two * succ b0) * inst2 P1 d (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) := by
  rw [inst2_LB, inst2_P1, inst2_P2]
  have hA : Γ ⊢[PRAAx] ap2 (sumF aK) (quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d)
      (sndT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) ≐
      latticeA (quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d) M α γ (succ b0) :=
    congrAp2 (sumF aK) (.eqRefl _) (snd_pair _ _)
  refine le_congr (congrMul (.eqRefl _) (congrMul (.eqRefl _) hA)).eqSymm (.eqRefl _) ?_
  refine .orE (zero_or_succ d) ?_ ?_
  · have g0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] monus one (monus two d) ≐ zero :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans gate_zero
    exact le_congr ((congrMul (.eqRefl _) ((congrMul g0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · let Δ : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : Δ ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have dm := div_mod_at (Γ := Δ) (x := fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) hd
    have hX1 : Δ ⊢[PRAAx] le (quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d)
        (d * quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d) :=
      le_of_eq_add (d := pred d * quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d)
        ((congrMul hd (.eqRefl _)).eqTrans (by ipra_ring))
    have hX2 : Δ ⊢[PRAAx] le (d * quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d)
        (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) :=
      le_of_eq_add (Prf.andE₁ dm)
    have hXM : Δ ⊢[PRAAx] le (quo (fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) d) M :=
      le_trans hX1 (le_trans (le_congr (.eqRefl _) (fst_pair _ _) hX2) hQM.wk)
    have k5 := Prf.andE₁ (lattice_core (Γ := Δ) hαγ.wk hγ.wk hXM)
    exact le_of_eq_add (k5_gate_aux (eq_add_of_le k5) (eq_add_of_le hαγ.wk))

/-! ## (K6) for the gated sums -/

/-- `Σ_{d ≤ Q} [2 ≤ d] ⌊Q/d⌋ ≤ Σ_{i < Q} ⌊Q/(i+1)⌋ = S(Q, Q)`. -/
theorem harm_part {Q z : PTm n} (hz : Γ ⊢[PRAAx] fstT z ≐ Q) :
    Γ ⊢[PRAAx] le (ap2 (sumF P1) (succ Q) z) (S Q Q) := by
  refine le_congr (sum_shift P1 Q z).eqSymm (.eqRefl _) ?_
  rw [inst2_P1]
  refine le_congr ((congrAdd ((congrMul gate_zero (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans
    (zero_add _)).eqSymm (.eqRefl _) ?_
  refine sum_le_params (shiftBody P1) hB z Q Q (.allI (.impI ?_))
  rw [inst2_shiftBody, inst2_P1, inst2_h]
  refine le_trans (gate_le _ _) (le_congr (.eqRefl _) ?_ (le_refl _))
  exact congrAp2 quoF (shift_fst_eq (N := Q) hz) (.eqRefl _)

/-- `⌊F/1⌋ = F`. -/
theorem quo_one_one (F : PTm n) : Γ ⊢[PRAAx] quo F (succ zero * succ zero) ≐ F := by
  have h1 : Γ ⊢[PRAAx] succ zero * succ (zero : PTm n) ≐ succ zero := one_mul _
  refine (congrAp2 quoF (.eqRefl _) h1).eqTrans ?_
  exact quo_eq (congrSucc (pred_succ _).eqSymm) ((one_mul F).eqSymm.eqTrans (add_zero _).eqSymm) (le_refl _)

/-- `t ≐ succ e` gives `t ≐ succ (pred t)`. -/
theorem pos_of_eq {t e : PTm n} (h : Γ ⊢[PRAAx] t ≐ succ e) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  h.eqTrans (congrSucc ((pred_succ e).eqSymm.eqTrans (congrPred h.eqSymm)))

/-- `[2 ≤ d] ⌊Q/d⌋² ≤ ⌊Q²/d²⌋` at `d = j + 2`. -/
theorem sq_point (j Q z : PTm n) (hz : Γ ⊢[PRAAx] fstT z ≐ Q) :
    Γ ⊢[PRAAx] le (inst2 P2 (succ (succ j)) z) (quo (Q * Q) (succ (succ j) * succ (succ j))) := by
  rw [inst2_P2]
  refine le_congr ((congrMul (gate_ss j).eqSymm (.eqRefl _)).eqTrans
    (congrMul (.eqRefl _) (.eqRefl _))) (.eqRefl _) ?_
  refine le_congr (one_mul _).eqSymm (.eqRefl _) ?_
  have hk : Γ ⊢[PRAAx] succ (succ j) * succ (succ j) ≐ succ (pred (succ (succ j) * succ (succ j))) :=
    pos_of_eq (e := succ (succ j) * succ j + succ j) (by ipra_ring)
  refine le_quo_of_mul_le hk ?_
  have dm := div_mod_at (Γ := Γ) (x := fstT z) (y := succ (succ j)) (c := succ j) (.eqRefl _)
  have hdX : Γ ⊢[PRAAx] le (succ (succ j) * quo (fstT z) (succ (succ j))) Q :=
    le_congr (.eqRefl _) hz (le_of_eq_add (Prf.andE₁ dm))
  refine le_congr ?_ (.eqRefl _) (sq_le_sq hdX)
  ipra_ring

/-- `Σ_{d ≤ Q} [2 ≤ d] ⌊Q/d⌋² + Q² ≤ T(Q, Q²) = Σ_{i < Q} ⌊Q²/(i+1)²⌋` for `Q = Q₁ + 1`. -/
theorem sq_part {Q Q₁ z : PTm n} (hz : Γ ⊢[PRAAx] fstT z ≐ Q) (hQ : Γ ⊢[PRAAx] Q ≐ succ Q₁) :
    Γ ⊢[PRAAx] le (ap2 (sumF P2) (succ Q) z + Q * Q) (T Q (Q * Q)) := by
  -- the left sum loses its terms `d = 0, 1`
  have eL : Γ ⊢[PRAAx] ap2 (sumF P2) (succ Q) z ≐ ap2 (sumF (shiftBody (shiftBody P2))) Q₁ z := by
    refine (sum_shift P2 Q z).eqTrans ?_
    rw [inst2_P2]
    refine (congrAdd ((congrMul gate_zero (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans
      ((zero_add _).eqTrans ?_)
    refine (congrAp2 (sumF (shiftBody P2)) hQ (.eqRefl _)).eqTrans ((sum_shift (shiftBody P2) Q₁ z).eqTrans ?_)
    rw [inst2_shiftBody, inst2_P2]
    exact (congrAdd ((congrMul gate_one (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_add _)
  -- the right sum is `Q² + Σ_{j < Q₁} ⌊Q²/(j+2)²⌋`
  have eR : Γ ⊢[PRAAx] T Q (Q * Q) ≐ Q * Q + ap2 (sumF (shiftBody sqB)) Q₁ (Q * Q) := by
    refine (congrAp2 (sumF sqB) hQ (.eqRefl _)).eqTrans ((sum_shift sqB Q₁ (Q * Q)).eqTrans ?_)
    rw [inst2_sq]
    exact congrAdd (quo_one_one _) (.eqRefl _)
  refine le_congr (congrAdd eL (.eqRefl _)).eqSymm eR.eqSymm ?_
  refine le_congr (.eqRefl _) (add_comm _ _) (add_le_add' ?_ (le_refl _))
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_shiftBody, inst2_shiftBody, inst2_shiftBody, inst2_sq]
  rw [show Syn.shift (Q * Q) = Syn.shift Q * Syn.shift Q by simp [Syn.shift]]
  exact sq_point _ _ _ (shift_fst_eq (N := Q₁) hz)

/-! ## The combination -/

/-- `Σ P2 + Q² ≤ T` and `4QT + 4Q² ≤ 7Q·Q²` give `Q(4 Σ P2 + 4Q) ≤ Q(3Q²)`, with atoms. -/
theorem sq_aux {Q P T : PTm n} (h1 : Γ ⊢[PRAAx] le (P + Q * Q) T)
    (h2 : Γ ⊢[PRAAx] le (num 4 * Q * T + num 4 * (Q * Q)) (num 7 * Q * (Q * Q))) :
    Γ ⊢[PRAAx] le (Q * (num 4 * P + num 4 * Q)) (Q * (num 3 * (Q * Q))) := by
  refine le_of_eq_add (d := num 4 * Q * monus T (P + Q * Q) +
    monus (num 7 * Q * (Q * Q)) (num 4 * Q * T + num 4 * (Q * Q))) ?_
  ipra_lc natEq (eq_add_of_le h2) + 4 * 𝔞 Q * natEq (eq_add_of_le h1)

/-- The final linear combination, with atoms. -/
theorem final_aux {Bad SLB SP1 SP2 B C D K Q : PTm n} (h1 : Γ ⊢[PRAAx] le Bad SLB)
    (h2 : Γ ⊢[PRAAx] le (two * B * SLB) (D * SP2 + C * SP1))
    (h3 : Γ ⊢[PRAAx] le (num 4 * SP2 + num 4 * Q) (num 3 * (Q * Q)))
    (h4 : Γ ⊢[PRAAx] le SP1 (K * Q)) :
    Γ ⊢[PRAAx] le (num 8 * B * Bad + num 4 * D * Q) (num 3 * D * (Q * Q) + num 4 * C * (K * Q)) := by
  refine le_of_eq_add (d := num 8 * B * monus SLB Bad + num 4 * monus (D * SP2 + C * SP1) (two * B * SLB) +
    D * monus (num 3 * (Q * Q)) (num 4 * SP2 + num 4 * Q) + num 4 * C * monus (K * Q) SP1) ?_
  ipra_lc 𝔞 D * natEq (eq_add_of_le h3) + 4 * 𝔞 C * natEq (eq_add_of_le h4) + 4 * natEq (eq_add_of_le h2) +
    8 * 𝔞 B * natEq (eq_add_of_le h1)

/-- The bad pairs of (K3): `8β B(Q) + 4DQ ≤ 3DQ² + 4(D + 2β)(k + 1)Q` for `Q = 2^k = Q₁ + 2 ≤ M`,
`α ≤ γ ≤ β = b₀ + 1` and `D = γ − α`. -/
theorem bad_bound {α γ b0 Q Q₁ M k : PTm n} (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hQM : Γ ⊢[PRAAx] le Q M) (hQ : Γ ⊢[PRAAx] Q ≐ pw two k) (hQ1 : Γ ⊢[PRAAx] Q ≐ succ (succ Q₁)) :
    Γ ⊢[PRAAx] le (num 8 * succ b0 * ap2 (sumF bqB) (succ Q) (pairT M (pairT α (pairT γ (succ b0)))) +
        num 4 * monus γ α * Q)
      (num 3 * monus γ α * (Q * Q) + num 4 * (monus γ α + two * succ b0) * (succ k * Q)) := by
  have hz : Γ ⊢[PRAAx] fstT (pairT Q (pairT M (pairT α (pairT γ (succ b0))))) ≐ Q := fst_pair _ _
  -- `B(Q) ≤ Σ_d [2 ≤ d] A(⌊Q/d⌋)`
  have h1 := bad_total (Γ := Γ) Q (pairT M (pairT α (pairT γ (succ b0))))
  -- (K5) summed over `d`
  have h2 : Γ ⊢[PRAAx] le (two * succ b0 * ap2 (sumF LB) (succ Q) (pairT Q (pairT M (pairT α (pairT γ (succ b0))))))
      (monus γ α * ap2 (sumF P2) (succ Q) (pairT Q (pairT M (pairT α (pairT γ (succ b0))))) +
        (monus γ α + two * succ b0) * ap2 (sumF P1) (succ Q) (pairT Q (pairT M (pairT α (pairT γ (succ b0)))))) := by
    refine sum_lin_le LB P2 P1 _ _ _ _ (succ Q) (.allI (.impI ?_))
    rw [show Syn.shift (pairT Q (pairT M (pairT α (pairT γ (succ b0))))) =
        pairT (Syn.shift Q) (pairT (Syn.shift M) (pairT (Syn.shift α) (pairT (Syn.shift γ) (succ (Syn.shift b0))))) by
          simp [Syn.shift],
      show Syn.shift (two * succ b0) = two * succ (Syn.shift b0) by simp [Syn.shift],
      show Syn.shift (monus γ α) = monus (Syn.shift γ) (Syn.shift α) by simp [Syn.shift],
      show Syn.shift (monus γ α + two * succ b0) = monus (Syn.shift γ) (Syn.shift α) + two * succ (Syn.shift b0) by
          simp [Syn.shift]]
    have hγ' := shift_le (N := succ Q) hγ
    rw [show Syn.shift (succ b0) = succ (Syn.shift b0) by simp [Syn.shift]] at hγ'
    exact per_d _ (shift_le hαγ) hγ' (shift_le hQM)
  -- (K6), the squares
  have h3 : Γ ⊢[PRAAx] le (num 4 * ap2 (sumF P2) (succ Q) (pairT Q (pairT M (pairT α (pairT γ (succ b0))))) +
      num 4 * Q) (num 3 * (Q * Q)) := by
    have sp := sq_part hz hQ1
    have sb : Γ ⊢[PRAAx] le (num 4 * Q * T Q (Q * Q) + num 4 * (Q * Q)) (num 7 * Q * (Q * Q)) :=
      le_congr (congrAdd (congrMul (congrMul (.eqRefl _) hQ1.eqSymm) (congrAp2 (sumF sqB) hQ1.eqSymm (.eqRefl _)))
          (.eqRefl _))
        (congrMul (congrMul (.eqRefl _) hQ1.eqSymm) (.eqRefl _)) (square_bound Q₁ (Q * Q))
    exact cancel_le (pos_of_eq hQ1) (sq_aux sp sb)
  -- (K6), the harmonic sum
  have h4 : Γ ⊢[PRAAx] le (ap2 (sumF P1) (succ Q) (pairT Q (pairT M (pairT α (pairT γ (succ b0))))))
      (succ k * Q) := by
    refine le_trans (harm_part hz) ?_
    have hu := harmonic_upper (Γ := Γ) k Q
    exact le_congr (congrAp2 (sumF hB) hQ.eqSymm (.eqRefl _)) (.eqRefl _) hu
  exact final_aux h1 h2 h3 h4

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadBound
