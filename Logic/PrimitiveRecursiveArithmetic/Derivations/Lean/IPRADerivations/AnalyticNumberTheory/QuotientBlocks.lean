import IPRADerivations.AnalyticNumberTheory.PrimorialUpper
import IPRADerivations.AnalyticNumberTheory.FourthRootSum
import IPRADerivations.AnalyticNumberTheory.MobiusFloor

/-!
# Quotient blocks

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`, Theorem `thm:floor-recurrence` ("Floor
recurrence and quotient blocks"), the block description in its proof: "For `1 ≤ q ≤ N`, the indices `a` giving
quotient `q` are exactly `q_N(q + 1) < a ≤ q_N(q)`", with `q_N(a) = ⌊N/a⌋`; and the count of the blocks used in
`computation.tex` ("at most `2⌊√N⌋` blocks").

* `mul_le_of_le_quo`: `t ≤ ⌊F/d⌋` gives `d t ≤ F` (the converse is `SumReindex.le_quo_of_mul_le`);
* **`block_of_quo`**: `⌊N/a⌋ = q` gives `⌊N/(q + 1)⌋ < a ≤ ⌊N/q⌋`, for `a, q ≥ 1`;
* **`quo_of_block`**: conversely `⌊N/(q + 1)⌋ < a ≤ ⌊N/q⌋` gives `⌊N/a⌋ = q`;
* `chB`, `Dc`: the bit `[⌊N/(i + 1)⌋ ≠ ⌊N/(i + 2)⌋]` and the number of changes among the first indices;
* `step_le`, `tele`: `D(x + 1) + ⌊N/(x + 2)⌋ ≤ D(x) + ⌊N/(x + 1)⌋` (a change lowers the quotient by at least
  one), hence `D(s + k) + ⌊N/(s + k + 1)⌋ ≤ D(s) + ⌊N/(s + 1)⌋`;
* **`block_count`**: the quotient `⌊N/a⌋`, `1 ≤ a ≤ N + 1`, changes at most `2⌊√N⌋` times: at most `⌊√N⌋`
  times for `a ≤ ⌊√N⌋`, and afterwards it is at most `⌊√N⌋` and nonincreasing.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.QuotientBlocks

open_ipra exports
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (row_short)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The block of a quotient -/

/-- `t ≤ ⌊F/d⌋` gives `d t ≤ F`. -/
theorem mul_le_of_le_quo {d t F : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (h : Γ ⊢[PRAAx] le t (quo F d)) : Γ ⊢[PRAAx] le (d * t) F := by
  have e := natEq (div_eq (Γ := Γ) (j := F) hd)
  ipra_le 𝔞 d * sl h + 𝔞 (rem F d) with e

theorem comm_le {a q N : PTm n} (h : Γ ⊢[PRAAx] le (a * q) N) : Γ ⊢[PRAAx] le (q * a) N :=
  le_congr (mul_comm a q) (.eqRefl _) h

alias succ_pos := Common.succ_pos

/-- **The block of the quotient `q`**: `⌊N/a⌋ = q` gives `⌊N/(q + 1)⌋ < a ≤ ⌊N/q⌋`. -/
theorem block_of_quo {a q N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (e : Γ ⊢[PRAAx] quo N a ≐ q) : Γ ⊢[PRAAx] lt (quo N (succ q)) a ⋏ le a (quo N q) := by
  have hqa : Γ ⊢[PRAAx] le q (quo N a) := le_congr (.eqRefl _) e.eqSymm (le_refl q)
  refine .andI ?_ (le_quo_of_mul_le hq (comm_le (mul_le_of_le_quo ha hqa)))
  refine .orE (lt_or_le (quo N (succ q)) a) Prf.hyp0 ?_
  have h : (le a (quo N (succ q)) :: Γ) ⊢[PRAAx] le a (quo N (succ q)) := Prf.hyp0
  have l : (le a (quo N (succ q)) :: Γ) ⊢[PRAAx] le (succ q) (quo N a) :=
    le_quo_of_mul_le ha.wk (comm_le (mul_le_of_le_quo (succ_pos q) h))
  exact lt_irrefl q _ (le_congr (.eqRefl _) e.wk l)

/-- **Conversely**: `⌊N/(q + 1)⌋ < a ≤ ⌊N/q⌋` gives `⌊N/a⌋ = q`. -/
theorem quo_of_block {a q N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (h1 : Γ ⊢[PRAAx] lt (quo N (succ q)) a) (h2 : Γ ⊢[PRAAx] le a (quo N q)) : Γ ⊢[PRAAx] quo N a ≐ q := by
  have lo : Γ ⊢[PRAAx] le q (quo N a) := le_quo_of_mul_le ha (comm_le (mul_le_of_le_quo hq h2))
  refine le_antisymm ?_ lo
  refine .orE (lt_or_le q (quo N a)) ?_ Prf.hyp0
  have h : (lt q (quo N a) :: Γ) ⊢[PRAAx] le (succ q) (quo N a) := Prf.hyp0
  have l : (lt q (quo N a) :: Γ) ⊢[PRAAx] le a (quo N (succ q)) :=
    le_quo_of_mul_le (succ_pos q) (comm_le (mul_le_of_le_quo ha.wk h))
  exact lt_irrefl (quo N (succ q)) _ (le_trans h1.wk l)

/-! ## The number of blocks -/

/-- `[⌊N/(i + 1)⌋ ≠ ⌊N/(i + 2)⌋]`, over `0 = i`, `1 = N`. -/
abbrev chB : PTm 2 := sg (monus (quo (var 1) (succ (var 0))) (quo (var 1) (succ (succ (var 0)))))

theorem inst2_chB (i N : PTm n) :
    inst2 chB i N = sg (monus (quo N (succ i)) (quo N (succ (succ i)))) := by
  simp only [inst2, PTm.subst_monus, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- The number of changes among the indices `i < x`. -/
abbrev Dc (x N : PTm n) : PTm n := ap2 (sumF chB) x N

theorem bit_alg {A B p : PTm n} (e : Γ ⊢[PRAAx] A ≐ B + succ p) : Γ ⊢[PRAAx] A ≐ (one + B) + p := by
  ipra_lc natEq e

/-- `[A ≠ B] + B ≤ A` for `B ≤ A`. -/
theorem bit_le {A B : PTm n} (h : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx] le (sg (monus A B) + B) A := by
  have eA := eq_add_of_le h
  refine .orE (zero_or_succ (monus A B)) ?_ ?_
  · have h0 : ((monus A B ≐ zero) :: Γ) ⊢[PRAAx] monus A B ≐ zero := Prf.hyp0
    exact le_congr ((zero_add B).eqSymm.eqTrans (congrAdd ((congrSg h0).eqTrans sg_zero).eqSymm (.eqRefl _)))
      (.eqRefl _) h.wk
  · have hs : ((monus A B ≐ succ (pred (monus A B))) :: Γ) ⊢[PRAAx] monus A B ≐ succ (pred (monus A B)) :=
      Prf.hyp0
    have s1 := (congrSg hs).eqTrans (sg_succ _)
    exact le_congr (congrAdd s1.eqSymm (.eqRefl _)) (.eqRefl _)
      (le_of_eq_add (bit_alg (eA.wk.eqTrans (congrAdd (.eqRefl _) hs))))

/-- A change lowers the quotient: `D(x + 1) + ⌊N/(x + 2)⌋ ≤ D(x) + ⌊N/(x + 1)⌋`. -/
theorem step_le (x N : PTm n) :
    Γ ⊢[PRAAx] le (Dc (succ x) N + quo N (succ (succ x))) (Dc x N + quo N (succ x)) := by
  have ss := sum_succ' (Γ := Γ) chB x N
  rw [inst2_chB] at ss
  have e := natEq ss
  have hBA : Γ ⊢[PRAAx] le (quo N (succ (succ x))) (quo N (succ x)) :=
    quo_anti (succ_pos x) (le_succ_self (succ x))
  have b := bit_le hBA
  ipra_le sl b with -e

/-- Variables: `0 = k`, `1 = s`, `2 = N`. -/
abbrev teleF : Fm PTm 3 :=
  le (ap2 (sumF chB) (var 1 + var 0) (var 2) + quo (var 2) (succ (var 1 + var 0)))
    (ap2 (sumF chB) (var 1) (var 2) + quo (var 2) (succ (var 1)))

theorem tele_congr {x x' s N : PTm n} (e : Γ ⊢[PRAAx] x ≐ x')
    (h : Γ ⊢[PRAAx] le (Dc x N + quo N (succ x)) (Dc s N + quo N (succ s))) :
    Γ ⊢[PRAAx] le (Dc x' N + quo N (succ x')) (Dc s N + quo N (succ s)) :=
  le_congr (congrAdd (congrAp2 (sumF chB) e (.eqRefl _)) (congrAp2 quoF (.eqRefl _) (congrSucc e))) (.eqRefl _) h

theorem tele_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] teleF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact tele_congr (add_zero (var 0)).eqSymm (le_refl _)
  · exact tele_congr (add_succ (var 1) (var 0)).eqSymm
      (le_trans (step_le (var 1 + var 0) (var 2)) (Prf.hyp0 (Γ := []) (φ := teleF)))

/-- `D(s + k) + ⌊N/(s + k + 1)⌋ ≤ D(s) + ⌊N/(s + 1)⌋`. -/
theorem tele (k s N : PTm n) :
    Γ ⊢[PRAAx] le (Dc (s + k) N + quo N (succ (s + k))) (Dc s N + quo N (succ s)) := by
  have i := inst (Γ := Γ) tele_open (![k, s, N] : Fin 3 → PTm n)
  simp only [teleF, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact i

theorem sq_succ (s : PTm n) : Γ ⊢[PRAAx] (s + one) * (s + one) ≐ succ s * succ s := by
  ipra_ring

/-- The first `s` indices contribute at most `s` changes. -/
theorem Dc_le (s N : PTm n) : Γ ⊢[PRAAx] le (Dc s N) s := by
  refine le_congr (.eqRefl _) (sum_ones s N) (sum_le chB one N s (.allI (.impI ?_)))
  rw [inst2_chB, inst2_oneB]
  exact sg_le1 _

/-- **The number of quotient blocks**: `⌊N/a⌋`, `1 ≤ a ≤ N + 1`, changes at most `2⌊√N⌋` times. -/
theorem block_count (N : PTm n) : Γ ⊢[PRAAx] le (Dc N N) (two * isqrt N) := by
  have hs : Γ ⊢[PRAAx] le (isqrt N) N := isqrt_le_self N
  have t := tele_congr (eq_add_of_le hs).eqSymm (tele (Γ := Γ) (monus N (isqrt N)) (isqrt N) N)
  have hD := Dc_le (Γ := Γ) (isqrt N) N
  have hq : Γ ⊢[PRAAx] le (quo N (succ (isqrt N))) (isqrt N) :=
    row_short (le_refl (isqrt N)) (lt_congr (.eqRefl _) (sq_succ _) (lt_isqrt_succ_sq N))
  ipra_le sl t + sl hD + sl hq + 𝔞 (quo N (succ N))

end LeanProofs.IPRA.AnalyticNumberTheory.QuotientBlocks
