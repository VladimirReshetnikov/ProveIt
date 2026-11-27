import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Topology.CollisionScales
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal

/-!
# Optimality of `1/√5` for the golden ratio (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, §"Optimality, with an
explicit finite denominator bound":

* (hw-norm): "For every `p ∈ ℤ, q ≥ 1`, `N = p² − pq − q² ≠ 0`" (`golden_norm`). The packet argues by
  reduction to lowest terms; here by a 2-adic descent: `p² = pq + q²` forces `p` and `q` to be even
  (`both_even`, by parity), so `2^j ∣ p, q` for every `j` (`descent`), and `j = q` contradicts
  `q < 2^q`.
* (hw-optimal-bound): "Let `c > 0` be rational with `5c² < 1`. Suppose `|φ − p/q| < c/q²`. … Therefore
  `q² < 2c²/(1 − 5c²)`" (`golden_optimal`).

The approximation hypothesis is stated without real numbers. For `f(z) = z² − z − 1 = (z − φ)(z − φ')`,
`r = p/q`, `ε = c/q²`, the condition `|φ − r| < ε` is `f(r − ε) < 0 < f(r + ε)` (for `p ≥ 1`), and with
`c = a/b`, `K = b²q²`, `s = abq`:

  `b²q⁴ f(r ± ε) = (p² − pq − q²) K + a² ± s (2p − q)`.

So the two hypotheses `H1 : p²K + a² + sq < (pq + q²)K + 2sp` and `H2 : (pq + q²)K + sq < p²K + a² + 2sp`
are exactly `f(r − ε) < 0` and `f(r + ε) > 0` cleared of denominators, and the conclusion
`b²q² < 5a²q² + 2a²` is `q² < 2c²/(1 − 5c²)`. The proof follows the packet: `|N| ≥ 1`; for `N ≥ 1`,
squaring `NK + a² < s(2p − q)` and `(2p − q)² = 4N + 5q²` give `(NK − a²)² < 5a²q²K`, hence the bound;
`N ≤ −1` is impossible, since `(|N|K + a²)² < 5a²q²K < K²`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.GoldenOptimal

open_ipra exports
open LeanProofs.IPRA.Topology.CollisionScales (lt_pw_two)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Small tools -/

/-- `1 ≤ 0` is absurd. -/
theorem absurd_one_zero (φ : Fm PTm n) (h : Γ ⊢[PRAAx] le one zero) : Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ (a := zero) ((monus_zero _).eqSymm.eqTrans h)

/-- `N A = N B`, `N ≥ 1` give `A = B`. -/
theorem cancel_eq {N A B : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h : Γ ⊢[PRAAx] N * A ≐ N * B) :
    Γ ⊢[PRAAx] A ≐ B :=
  le_antisymm (cancel_le hN (le_congr (.eqRefl _) h (le_refl _)))
    (cancel_le hN (le_congr (.eqRefl _) h.eqSymm (le_refl _)))

/-- `t ≐ succ e` gives `t ≐ succ (pred t)`. -/
theorem pos_of_eq {t e : PTm n} (h : Γ ⊢[PRAAx] t ≐ succ e) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  h.eqTrans (congrSucc ((pred_succ e).eqSymm.eqTrans (congrPred h.eqSymm)))

/-- `⌊x / B⌋ = u` when `x = B u`, `B ≥ 1`. -/
theorem quo_mul {x B u : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (h : Γ ⊢[PRAAx] x ≐ B * u) :
    Γ ⊢[PRAAx] quo x B ≐ u :=
  Division.quo_eq_mul hB h

/-! ## The norm `p² − pq − q²` does not vanish -/

/-- If `P² = PQ + Q²` then `P` and `Q` are even. -/
theorem both_even {P Q : PTm n} (h : Γ ⊢[PRAAx] P * P ≐ P * Q + Q * Q) :
    Γ ⊢[PRAAx] (P ≐ two * half P) ⋏ (Q ≐ two * half Q) := by
  have hP := half_par (Γ := Γ) P
  have hQ := half_par (Γ := Γ) Q
  refine .orE (par_cases (Γ := Γ) P) ?_ ?_
  · let Δ : List (Fm PTm n) := (par P ≐ zero) :: Γ
    have eP : Δ ⊢[PRAAx] P ≐ two * half P := hP.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
    refine .orE (par_cases (Γ := Δ) Q) ?_ ?_
    · have eQ : ((par Q ≐ zero) :: Δ) ⊢[PRAAx] Q ≐ two * half Q :=
        hQ.wk.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
      exact .andI eP.wk eQ
    · -- `P` even, `Q` odd
      let Δ' : List (Fm PTm n) := (par Q ≐ one) :: Δ
      have eQ : Δ' ⊢[PRAAx] Q ≐ two * half Q + one := hQ.wk.wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
      have h' := natEq ((congrMul eP.wk eP.wk).eqSymm.eqTrans
        (h.wk.wk.eqTrans (congrAdd (congrMul eP.wk eQ) (congrMul eQ eQ))))
      refine even_ne_odd (k := two * half P * half P)
        (m := two * half P * half Q + half P + two * half Q * half Q + two * half Q) _ ?_
      ipra_lc h'
  · let Δ : List (Fm PTm n) := (par P ≐ one) :: Γ
    have eP : Δ ⊢[PRAAx] P ≐ two * half P + one := hP.wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
    refine .orE (par_cases (Γ := Δ) Q) ?_ ?_
    · -- `P` odd, `Q` even
      let Δ' : List (Fm PTm n) := (par Q ≐ zero) :: Δ
      have eQ : Δ' ⊢[PRAAx] Q ≐ two * half Q := hQ.wk.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
      have h' := natEq ((congrMul eP.wk eP.wk).eqSymm.eqTrans
        (h.wk.wk.eqTrans (congrAdd (congrMul eP.wk eQ) (congrMul eQ eQ))))
      refine even_ne_odd (k := (two * half P + one) * half Q + two * half Q * half Q)
        (m := two * half P * half P + two * half P) _ ?_
      ipra_lc -h'
    · -- both odd
      let Δ' : List (Fm PTm n) := (par Q ≐ one) :: Δ
      have eQ : Δ' ⊢[PRAAx] Q ≐ two * half Q + one := hQ.wk.wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
      have h' := natEq ((congrMul eP.wk eP.wk).eqSymm.eqTrans
        (h.wk.wk.eqTrans (congrAdd (congrMul eP.wk eQ) (congrMul eQ eQ))))
      refine even_ne_odd (k := two * half P * half Q + half P + num 3 * half Q + two * half Q * half Q + one)
        (m := two * half P * half P + two * half P) _ ?_
      ipra_lc -h'

/-- The descent invariant: `p² = pq + q²` gives `2^j ∣ p` and `2^j ∣ q`. -/
def nInv (j p q : PTm n) : Fm PTm n :=
  (p * p ≐ p * q + q * q) ⟶ ((p ≐ pw two j * quo p (pw two j)) ⋏ (q ≐ pw two j * quo q (pw two j)))

ipra_subst nInv [subst_ap2]

theorem nInv_QF (j p q : PTm n) : (nInv j p q).QF := by
  unfold nInv; exact ⟨trivial, trivial, trivial⟩

theorem pw_two_pos (j : PTm n) : Γ ⊢[PRAAx] pw two j ≐ succ (pred (pw two j)) := pw_pos one j

/-- The induction step. -/
theorem descent_step {j p q : PTm n} (ih : Γ ⊢[PRAAx] nInv j p q) : Γ ⊢[PRAAx] nInv (succ j) p q := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := (p * p ≐ p * q + q * q) :: Γ
  have hE : Δ ⊢[PRAAx] p * p ≐ p * q + q * q := Prf.hyp0
  have d := Prf.impE ih.wk hE
  have dp : Δ ⊢[PRAAx] p ≐ pw two j * quo p (pw two j) := Prf.andE₁ d
  have dq : Δ ⊢[PRAAx] q ≐ pw two j * quo q (pw two j) := Prf.andE₂ d
  -- the quotients satisfy the same equation
  have hA := pw_two_pos (Γ := Δ) j
  have hN : Δ ⊢[PRAAx] pw two j * pw two j ≐ succ (pred (pw two j * pw two j)) := by
    refine pos_of_eq (e := pred (pw two j) * succ (pred (pw two j)) + pred (pw two j)) ?_
    refine (congrMul hA hA).eqTrans ?_
    ipra_ring
  have hPQ : Δ ⊢[PRAAx] quo p (pw two j) * quo p (pw two j) ≐
      quo p (pw two j) * quo q (pw two j) + quo q (pw two j) * quo q (pw two j) := by
    refine cancel_eq hN ?_
    ipra_lc natEq ((congrMul dp dp).eqSymm.eqTrans (hE.eqTrans (congrAdd (congrMul dp dq) (congrMul dq dq))))
  have ev := both_even hPQ
  have hB := pw_two_pos (Γ := Δ) (succ j)
  have es := pw_succ (Γ := Δ) two j
  -- `p = 2^{j+1} ⌊P/2⌋`
  have xp : Δ ⊢[PRAAx] p ≐ pw two (succ j) * half (quo p (pw two j)) := by
    refine dp.eqTrans ((congrMul (.eqRefl _) (Prf.andE₁ ev)).eqTrans ?_)
    refine .eqTrans ?_ (congrMul es (.eqRefl _)).eqSymm
    ipra_ring
  have xq : Δ ⊢[PRAAx] q ≐ pw two (succ j) * half (quo q (pw two j)) := by
    refine dq.eqTrans ((congrMul (.eqRefl _) (Prf.andE₂ ev)).eqTrans ?_)
    refine .eqTrans ?_ (congrMul es (.eqRefl _)).eqSymm
    ipra_ring
  exact .andI (xp.eqTrans (congrMul (.eqRefl _) (quo_mul hB xp).eqSymm))
    (xq.eqTrans (congrMul (.eqRefl _) (quo_mul hB xq).eqSymm))

/-- The base: `2⁰ = 1` divides everything. -/
theorem descent_base (p q : PTm n) : Γ ⊢[PRAAx] nInv zero p q := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := (p * p ≐ p * q + q * q) :: Γ
  have h0 := pw_zero (Γ := Δ) (two : PTm n)
  have hB := pw_two_pos (Γ := Δ) (zero : PTm n)
  have one_x : ∀ x : PTm n, Δ ⊢[PRAAx] x ≐ pw two zero * quo x (pw two zero) := fun x => by
    have e : Δ ⊢[PRAAx] x ≐ pw two zero * x := (one_mul x).eqSymm.eqTrans (congrMul h0.eqSymm (.eqRefl _))
    exact e.eqTrans (congrMul (.eqRefl _) (quo_mul hB e).eqSymm)
  exact .andI (one_x p) (one_x q)

/-- `p² = pq + q²` gives `2^j ∣ p, q` for every `j`. -/
theorem descent (j p q : PTm n) : Γ ⊢[PRAAx] nInv j p q := by
  have hall : Γ ⊢[PRAAx] Fm.all (nInv (var 0) (Syn.shift p) (Syn.shift q)) := by
    refine PRA.qfInd _ (nInv_QF _ _ _) ?_ ?_
    · rw [subst_nInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact descent_base _ _
    · rw [subst_nInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact descent_step Prf.hyp0
  have a := Prf.allE j hall
  rw [subst_nInv] at a
  simpa [Syn.subst_inst_shift] using a

/-- (hw-norm): `p² ≠ pq + q²` for `q ≥ 1`. -/
theorem golden_norm {p q : PTm n} (φ : Fm PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (h : Γ ⊢[PRAAx] p * p ≐ p * q + q * q) : Γ ⊢[PRAAx] φ := by
  have d := Prf.andE₂ (Prf.impE (descent q p q) h)
  have hlt := lt_pw_two (Γ := Γ) q
  refine .orE (zero_or_succ (quo q (pw two q))) ?_ ?_
  · have e0 := natEq (Prf.hyp0 : ((quo q (pw two q) ≐ zero) :: Γ) ⊢[PRAAx] quo q (pw two q) ≐ zero)
    refine absurd_one_zero _ ?_
    have hq' : ((quo q (pw two q) ≐ zero) :: Γ) ⊢[PRAAx] le one q := hq.wk
    have ed' := natEq (d.wk : ((quo q (pw two q) ≐ zero) :: Γ) ⊢[PRAAx] q ≐ pw two q * quo q (pw two q))
    ipra_le sl hq' with ed' + 𝔞 (pw two q) * e0
  · let Δ : List (Fm PTm n) := (quo q (pw two q) ≐ succ (pred (quo q (pw two q)))) :: Γ
    have e1 := natEq (Prf.hyp0 : Δ ⊢[PRAAx] quo q (pw two q) ≐ succ (pred (quo q (pw two q))))
    refine absurd_one_zero _ ?_
    have hlt' : Δ ⊢[PRAAx] lt q (pw two q) := hlt.wk
    have ed' := natEq (d.wk : Δ ⊢[PRAAx] q ≐ pw two q * quo q (pw two q))
    ipra_le sl hlt' + 𝔞 (pw two q) * 𝔞 (pred (quo q (pw two q))) with ed' + 𝔞 (pw two q) * e1

/-! ## The optimality bound -/

/-- Squaring a strict inequality with an offset: `X + c < d` gives `X² + 2dc < d² + c²`. -/
theorem sq_gap {X c d : PTm n} (h : Γ ⊢[PRAAx] lt (X + c) d) :
    Γ ⊢[PRAAx] lt (X * X + two * d * c) (d * d + c * c) := by
  ipra_le 2 * 𝔞 X + 2 * sl h * (𝔞 X + 1) + sl h * sl h

/-- The case `N = p² − pq − q² ≥ 1`. -/
theorem pos_case {p q a b : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hN : Γ ⊢[PRAAx] lt (p * q + q * q) (p * p))
    (H1 : Γ ⊢[PRAAx] lt (p * p * (b * b * (q * q)) + a * a + a * b * q * q)
      ((p * q + q * q) * (b * b * (q * q)) + two * (a * b * q) * p)) :
    Γ ⊢[PRAAx] lt (b * b * (q * q)) (num 5 * (a * a) * (q * q) + two * (a * a)) := by
  have hle : Γ ⊢[PRAAx] le (p * q + q * q) (p * p) := le_trans (le_succ_self _) hN
  have eN := natEq (eq_add_of_le hle)
  have hn : Γ ⊢[PRAAx] le one (monus (p * p) (p * q + q * q)) := by ipra_le sl hN with eN
  -- `NK + a² + sq < 2sp`
  have F1 : Γ ⊢[PRAAx] lt (monus (p * p) (p * q + q * q) * (b * b * (q * q)) + a * a + a * b * q * q)
      (two * (a * b * q) * p) := by
    ipra_le sl H1 with 𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q) * eN
  have F2 := sq_gap (X := monus (p * p) (p * q + q * q) * (b * b * (q * q)) + a * a) (c := a * b * q * q)
    (d := two * (a * b * q) * p) F1
  refine .orE (lt_or_le (b * b * (q * q)) (num 5 * (a * a) * (q * q) + two * (a * a))) Prf.hyp0 ?_
  let Δ : List (Fm PTm n) := le (num 5 * (a * a) * (q * q) + two * (a * a)) (b * b * (q * q)) :: Γ
  have hR : Δ ⊢[PRAAx] le (num 5 * (a * a) * (q * q) + two * (a * a)) (b * b * (q * q)) := Prf.hyp0
  refine absurd_one_zero _ ?_
  have F2' : Δ ⊢[PRAAx] lt _ _ := F2.wk
  have hn' : Δ ⊢[PRAAx] le one (monus (p * p) (p * q + q * q)) := hn.wk
  have ha' : Δ ⊢[PRAAx] le one a := ha.wk
  have eN' := natEq ((eq_add_of_le hle).wk : Δ ⊢[PRAAx] _ ≐ _)
  -- `K ≥ a² + 1` follows from `K ≥ 5a²q² + 2a²`
  have hK : Δ ⊢[PRAAx] le (succ (a * a)) (b * b * (q * q)) := by
    ipra_le sl hR + 5 * 𝔞 a * 𝔞 a * 𝔞 q * 𝔞 q + sl ha' * (𝔞 a + 1)
  ipra_le sl F2' + sl hR * 𝔞 (b * b * (q * q)) + 𝔞 a * 𝔞 a * 𝔞 a * 𝔞 a +
      sl hn' * 𝔞 (b * b * (q * q)) * (sl hn' * 𝔞 (b * b * (q * q)) + 2 * sl hK + 2)
    with (4 * (𝔞 a * 𝔞 b * 𝔞 q) * (𝔞 a * 𝔞 b * 𝔞 q)) * eN'

/-- The case `N = p² − pq − q² ≤ −1` is impossible. -/
theorem neg_case {p q a b : PTm n} (φ : Fm PTm n)
    (hab : Γ ⊢[PRAAx] lt (num 5 * (a * a)) (b * b)) (hN : Γ ⊢[PRAAx] lt (p * p) (p * q + q * q))
    (H1 : Γ ⊢[PRAAx] lt (p * p * (b * b * (q * q)) + a * a + a * b * q * q)
      ((p * q + q * q) * (b * b * (q * q)) + two * (a * b * q) * p))
    (H2 : Γ ⊢[PRAAx] lt ((p * q + q * q) * (b * b * (q * q)) + a * b * q * q)
      (p * p * (b * b * (q * q)) + a * a + two * (a * b * q) * p)) :
    Γ ⊢[PRAAx] φ := by
  have hle : Γ ⊢[PRAAx] le (p * p) (p * q + q * q) := le_trans (le_succ_self _) hN
  have eM := natEq (eq_add_of_le hle)
  have hm : Γ ⊢[PRAAx] le one (monus (p * q + q * q) (p * p)) := by ipra_le sl hN with eM
  refine .orE (lt_or_le (monus (p * q + q * q) (p * p) * (b * b * (q * q))) (a * a)) ?_ ?_
  · -- `mK < a²`: `(a² − mK) + sq < 2sp` from `H1`
    let Δ : List (Fm PTm n) := lt (monus (p * q + q * q) (p * p) * (b * b * (q * q))) (a * a) :: Γ
    have hy : Δ ⊢[PRAAx] le (monus (p * q + q * q) (p * p) * (b * b * (q * q))) (a * a) :=
      le_trans (le_succ_self _) Prf.hyp0
    have eY := natEq (eq_add_of_le hy)
    have eM' := natEq ((eq_add_of_le hle).wk : Δ ⊢[PRAAx] _ ≐ _)
    have H1' : Δ ⊢[PRAAx] lt _ _ := H1.wk
    have G : Δ ⊢[PRAAx] lt (monus (a * a) (monus (p * q + q * q) (p * p) * (b * b * (q * q))) + a * b * q * q)
        (two * (a * b * q) * p) := by
      ipra_le sl H1' with eY - 𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q) * eM'
    have S := sq_gap G
    have hm' : Δ ⊢[PRAAx] le one (monus (p * q + q * q) (p * p)) := hm.wk
    have hab' : Δ ⊢[PRAAx] lt (num 5 * (a * a)) (b * b) := hab.wk
    refine absurd_one_zero _ ?_
    ipra_le sl S + 𝔞 q * 𝔞 q * (sl hab' + 1) * 𝔞 (b * b * (q * q)) +
        sl hm' * (sl hm' + 2) * 𝔞 (b * b * (q * q)) * 𝔞 (b * b * (q * q)) +
        2 * (sl hm' + 1) * 𝔞 (b * b * (q * q)) * (𝔞 a * 𝔞 a) + 𝔞 a * 𝔞 a * 𝔞 a * 𝔞 a
      with (4 * (𝔞 a * 𝔞 a) * (𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q))) * eM' -
        (𝔞 (monus (a * a) (monus (p * q + q * q) (p * p) * (b * b * (q * q)))) + 𝔞 a * 𝔞 a -
          𝔞 (monus (p * q + q * q) (p * p)) * (𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q))) * eY
  · -- `mK ≥ a²`: `(mK − a²) + sq < 2sp` from `H2`
    let Δ : List (Fm PTm n) := le (a * a) (monus (p * q + q * q) (p * p) * (b * b * (q * q))) :: Γ
    have hy : Δ ⊢[PRAAx] le (a * a) (monus (p * q + q * q) (p * p) * (b * b * (q * q))) := Prf.hyp0
    have eY := natEq (eq_add_of_le hy)
    have eM' := natEq ((eq_add_of_le hle).wk : Δ ⊢[PRAAx] _ ≐ _)
    have H2' : Δ ⊢[PRAAx] lt _ _ := H2.wk
    have G : Δ ⊢[PRAAx] lt (monus (monus (p * q + q * q) (p * p) * (b * b * (q * q))) (a * a) + a * b * q * q)
        (two * (a * b * q) * p) := by
      ipra_le sl H2' with eY + 𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q) * eM'
    have S := sq_gap G
    have hm' : Δ ⊢[PRAAx] le one (monus (p * q + q * q) (p * p)) := hm.wk
    have hab' : Δ ⊢[PRAAx] lt (num 5 * (a * a)) (b * b) := hab.wk
    refine absurd_one_zero _ ?_
    ipra_le sl S + 𝔞 q * 𝔞 q * (sl hab' + 1) * 𝔞 (b * b * (q * q)) +
        sl hm' * (sl hm' + 2) * 𝔞 (b * b * (q * q)) * 𝔞 (b * b * (q * q)) +
        2 * (sl hm' + 1) * 𝔞 (b * b * (q * q)) * (𝔞 a * 𝔞 a) + 𝔞 a * 𝔞 a * 𝔞 a * 𝔞 a
      with (4 * (𝔞 a * 𝔞 a) * (𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q))) * eM' -
        (𝔞 (monus (monus (p * q + q * q) (p * p) * (b * b * (q * q))) (a * a)) +
          𝔞 (monus (p * q + q * q) (p * p)) * (𝔞 b * 𝔞 b * (𝔞 q * 𝔞 q)) - 𝔞 a * 𝔞 a) * eY

/-- (hw-optimal-bound): for `c = a/b > 0` with `5c² < 1`, `q ≥ 1`, and `p/q` with `|φ − p/q| < c/q²`
(the hypotheses `H1`, `H2`: `f(p/q ∓ c/q²) ≶ 0` cleared of denominators), `b²q² < 5a²q² + 2a²`,
i.e. `q² < 2c²/(1 − 5c²)`. -/
theorem golden_optimal {p q a b : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hq : Γ ⊢[PRAAx] le one q)
    (hab : Γ ⊢[PRAAx] lt (num 5 * (a * a)) (b * b))
    (H1 : Γ ⊢[PRAAx] lt (p * p * (b * b * (q * q)) + a * a + a * b * q * q)
      ((p * q + q * q) * (b * b * (q * q)) + two * (a * b * q) * p))
    (H2 : Γ ⊢[PRAAx] lt ((p * q + q * q) * (b * b * (q * q)) + a * b * q * q)
      (p * p * (b * b * (q * q)) + a * a + two * (a * b * q) * p)) :
    Γ ⊢[PRAAx] lt (b * b * (q * q)) (num 5 * (a * a) * (q * q) + two * (a * a)) := by
  refine .orE (lt_or_le (p * p) (p * q + q * q)) ?_ ?_
  · exact neg_case _ hab.wk Prf.hyp0 H1.wk H2.wk
  · refine .orE (lt_or_le (p * q + q * q) (p * p)) ?_ ?_
    · exact pos_case ha.wk.wk Prf.hyp0 H1.wk.wk
    · exact golden_norm _ hq.wk.wk (le_antisymm Prf.hyp0 Prf.hyp1)

/-- Variables `0 = p`, `1 = q`, `2 = a`, `3 = b`. -/
def optimalFormula : Fm PTm 4 :=
  le one (var 2) ⟶ (le one (var 1) ⟶ (lt (num 5 * (var 2 * var 2)) (var 3 * var 3) ⟶
    (lt (var 0 * var 0 * (var 3 * var 3 * (var 1 * var 1)) + var 2 * var 2 + var 2 * var 3 * var 1 * var 1)
        ((var 0 * var 1 + var 1 * var 1) * (var 3 * var 3 * (var 1 * var 1)) + two * (var 2 * var 3 * var 1) * var 0) ⟶
      (lt ((var 0 * var 1 + var 1 * var 1) * (var 3 * var 3 * (var 1 * var 1)) + var 2 * var 3 * var 1 * var 1)
          (var 0 * var 0 * (var 3 * var 3 * (var 1 * var 1)) + var 2 * var 2 + two * (var 2 * var 3 * var 1) * var 0) ⟶
        lt (var 3 * var 3 * (var 1 * var 1)) (num 5 * (var 2 * var 2) * (var 1 * var 1) + two * (var 2 * var 2))))))

private theorem hyp3' {Δ : List (Fm PTm 4)} {a b c φ : Fm PTm 4} : (a :: b :: c :: φ :: Δ) ⊢[PRAAx] φ :=
  Prf.hyp (by simp)

private theorem hyp4' {Δ : List (Fm PTm 4)} {a b c d φ : Fm PTm 4} : (a :: b :: c :: d :: φ :: Δ) ⊢[PRAAx] φ :=
  Prf.hyp (by simp)

/-- (hw-optimal-bound), as a closed sentence of iPRA. -/
theorem optimal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 optimalFormula :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (golden_optimal hyp4' hyp3' hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.DiophantineNumberTheory.GoldenOptimal
