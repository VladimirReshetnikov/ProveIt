import IPRADerivations.Probability.ProductPower
import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Exponentials and products of finite sets (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The category of finite sets has
exponentials in iPRA", theorem "Finite exponentials": `[m]^[n] = [m^n]`.

An arrow `[n] → [m]` is a table of `n` entries below `m`; for `m ≥ 1` it is coded by
`c = ∑_{j<n} h(j) m^j < m^n`, and evaluation is the digit
`ev(c, j) = ⌊c / m^j⌋ mod m` (`dg m j c` of `Probability/ProductPower`).

A table is given by an arbitrary term `t(j, p)` (variables `0 = j`, `1 = p`, a parameter); its
`j`-th entry is `t(j, p) mod m`, so that every term denotes a table into `[m]` and no bounded
hypothesis on `t` is needed. If `t(j, p) < m` the entry is `t(j, p)` itself (`rem_of_lt`).

* `code t N m p = ∑_{j<N} (t(j, p) mod m) m^j` is the curried code (`code_zero`, `code_succ`);
* `code_lt`: `code t N m p < m^N` for `m ≥ 1`: the code is an element of `[m^N]`;
* `ev_curry`: `ev(code t N m p, j) = t(j, p) mod m` for `j < N` (the first inverse law);
  `ev_curry_of_lt`: `= t(j, p)` when `t(j, p) < m`;
* `recon`: `∑_{j<N} ev(c, j) m^j + ⌊c / m^N⌋ m^N = c` for every `c`;
* `curry_ev`: for `c < m^N`, currying the evaluation table of `c` recovers `c` (the second
  inverse law); `dg_lt`: `ev(c, j) < m`.

With a parameter `k < z` in `p` these two laws are the universal property of the exponential:
`ev(curry h(k), j) = h(k, j)`, and `curry (ev ∘ (u × 1)) = u` entrywise. Closed forms:
`ev_curry_closed`, `curry_ev_closed`.

The binary product `[n] × [m] ≅ [nm]` by `(i, j) ↦ i m + j`:

* `pair_lt`: `i m + j < n m` for `i < n`, `j < m`;
* `pair_fst`, `pair_snd`: the projections `⌊k / m⌋`, `k mod m` of a pair;
* `fst_lt`, `snd_lt`, `pair_eta`: for `k < n m` the projections are in range and
  `k = ⌊k / m⌋ m + (k mod m)` (uniqueness of the pairing).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteSetExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.BlockSum (qr_block)
open LeanProofs.IPRA.Probability.ProductPower (dg dg_low dg_top rem_lt'' div_eq')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dmu digit_step quo_small)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Currying a table -/

/-- `(t(j, p) mod m) m^j`, over `0 = j`, `1 = ⟨m, p⟩`. -/
abbrev cB (t : PTm 2) : PTm 2 :=
  rem (inst2 t (var 0) (sndT (var 1))) (fstT (var 1)) * pw (fstT (var 1)) (var 0)

/-- The code `∑_{j<N} (t(j, p) mod m) m^j` of the table `t(·, p)` of length `N`. -/
abbrev code (t : PTm 2) (N m p : PTm n) : PTm n := ap2 (sumF (cB t)) N (pairT m p)

theorem cB_at (t : PTm 2) (j m p : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB t) j (pairT m p) ≐ rem (inst2 t j p) m * pw m j := by
  have e : inst2 (cB t) j (pairT m p) =
      rem (inst2 t j (sndT (pairT m p))) (fstT (pairT m p)) * pw (fstT (pairT m p)) j := by
    show Syn.subst ![j, pairT m p] (cB t) = _
    simp
  rw [e]
  exact congrMul (congrAp2 remF (congrInst2 t (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
    (congrPw (fst_pair _ _) (.eqRefl _))

theorem code_zero (t : PTm 2) (m p : PTm n) : Γ ⊢[PRAAx] code t zero m p ≐ zero :=
  sum_zero _ _

theorem code_succ (t : PTm 2) (N m p : PTm n) :
    Γ ⊢[PRAAx] code t (succ N) m p ≐ rem (inst2 t N p) m * pw m N + code t N m p :=
  ((sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (cB_at t N m p))).eqTrans (add_comm _ _)

/-! ## The code is below `m^N` -/

private theorem code_lt_step (t : PTm 2) {N m p : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (ih : Γ ⊢[PRAAx] lt (code t N m p) (pw m N)) :
    Γ ⊢[PRAAx] lt (code t (succ N) m p) (pw m (succ N)) := by
  have he : Γ ⊢[PRAAx] lt (rem (inst2 t N p) m) m := rem_lt'' hm _
  refine le_of_eq_add (d := pw m N * monus m (succ (rem (inst2 t N p) m)) +
    monus (pw m N) (succ (code t N m p))) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) m N) - natEq (code_succ (Γ := Γ) t N m p) + 𝔞 (pw m N) * natEq (eq_add_of_le he) +
    natEq (eq_add_of_le ih)

/-- Variables: `0 = N`, `1 = m`, `2 = p`. -/
private abbrev ltF (t : PTm 2) : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    lt (ap2 (sumF (cB t)) (var 0) (pairT (var 1) (var 2))) (pw (var 1) (var 0))

private theorem code_lt₀ (t : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] ltF t := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_pairT, PTm.subst_pred,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (lt_congr (code_zero t _ _).eqSymm (pw_zero _).eqSymm (le_refl one))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_pairT, PTm.subst_pred,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (code_lt_step t Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- The code of a table of length `N` into `[m]` is an element of `[m^N]`. -/
theorem code_lt (t : PTm 2) {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N p : PTm n) :
    Γ ⊢[PRAAx] lt (code t N m p) (pw m N) := by
  have h := inst (Γ := Γ) (code_lt₀ t) (![N, m, p] : Fin 3 → PTm n)
  simp at h
  exact .impE h hm

/-! ## Evaluation of a curried table -/

private theorem ev_step (t : PTm 2) {N j m p : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hj : Γ ⊢[PRAAx] lt j (succ N))
    (ih : Γ ⊢[PRAAx] lt j N ⟶ (dg m j (code t N m p) ≐ rem (inst2 t j p) m)) :
    Γ ⊢[PRAAx] dg m j (code t (succ N) m p) ≐ rem (inst2 t j p) m := by
  have cs := code_succ (Γ := Γ) t N m p
  have hle : Γ ⊢[PRAAx] le j N := (succ_monus_succ j N).eqSymm.eqTrans hj
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · -- `j < N`: the new top digit is not seen
    have h₁ : (lt j N :: Γ) ⊢[PRAAx]
        dg m j (rem (inst2 t N p) m * pw m N + code t N m p) ≐ dg m j (code t N m p) :=
      dg_low hm.wk Prf.hyp0
    have c₁ : (lt j N :: Γ) ⊢[PRAAx] dg m j (code t (succ N) m p) ≐
        dg m j (rem (inst2 t N p) m * pw m N + code t N m p) :=
      congrAp2 remF (congrAp2 quoF cs.wk (.eqRefl _)) (.eqRefl _)
    exact c₁.eqTrans (h₁.eqTrans (.impE ih.wk Prf.hyp0))
  · -- `j = N`: the top digit
    have hjN : ((j ≐ N) :: Γ) ⊢[PRAAx] j ≐ N := Prf.hyp0
    have h₂ : ((j ≐ N) :: Γ) ⊢[PRAAx]
        dg m N (rem (inst2 t N p) m * pw m N + code t N m p) ≐ rem (inst2 t N p) m :=
      dg_top hm.wk (rem_lt'' hm.wk _) (code_lt t hm.wk N p)
    have c₂ : ((j ≐ N) :: Γ) ⊢[PRAAx] dg m j (code t (succ N) m p) ≐
        dg m N (rem (inst2 t N p) m * pw m N + code t N m p) :=
      congrAp2 remF (congrAp2 quoF cs.wk (congrPw (.eqRefl _) hjN)) (.eqRefl _)
    exact c₂.eqTrans (h₂.eqTrans
      (congrAp2 remF (congrInst2 t hjN.eqSymm (.eqRefl _)) (.eqRefl _)))

/-- Variables: `0 = N`, `1 = j`, `2 = m`, `3 = p`. -/
private abbrev evF (t : PTm 2) : Fm PTm 4 :=
  (var 2 ≐ succ (pred (var 2))) ⟶ lt (var 1) (var 0) ⟶
    (dg (var 2) (var 1) (ap2 (sumF (cB t)) (var 0) (pairT (var 2) (var 3))) ≐
      rem (inst2 t (var 1) (var 3)) (var 2))

private theorem ev₀ (t : PTm 2) : ([] : List (Fm PTm 4)) ⊢[PRAAx] evF t := by
  refine ind _ ⟨trivial, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_pairT, subst_inst2,
      PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (lt_zero_absurd _ Prf.hyp0))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_pairT, subst_inst2,
      PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (ev_step t Prf.hyp1 Prf.hyp0 (.impE hyp2 Prf.hyp1)))

/-- The first inverse law: the `j`-th digit of the code of a table is its `j`-th entry. -/
theorem ev_curry (t : PTm 2) {N j m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hj : Γ ⊢[PRAAx] lt j N) (p : PTm n) :
    Γ ⊢[PRAAx] dg m j (code t N m p) ≐ rem (inst2 t j p) m := by
  have h := inst (Γ := Γ) (ev₀ t) (![N, j, m, p] : Fin 4 → PTm n)
  simp at h
  exact .impE (.impE h hm) hj

/-- `r mod K = r` for `r < K`. -/
theorem rem_of_lt {K r : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (h : Γ ⊢[PRAAx] lt r K) :
    Γ ⊢[PRAAx] rem r K ≐ r :=
  Prf.andE₂ (dmu hK (q := zero) (by ipra_ring) h)

/-- The first inverse law for a table whose entry is already below `m`. -/
theorem ev_curry_of_lt (t : PTm 2) {N j m p : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hj : Γ ⊢[PRAAx] lt j N) (ht : Γ ⊢[PRAAx] lt (inst2 t j p) m) :
    Γ ⊢[PRAAx] dg m j (code t N m p) ≐ inst2 t j p :=
  (ev_curry t hm hj p).eqTrans (rem_of_lt hm ht)

/-- Evaluation lands in `[m]`. -/
theorem dg_lt {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (j c : PTm n) :
    Γ ⊢[PRAAx] lt (dg m j c) m := rem_lt'' hm _

/-! ## Currying the evaluation table -/

/-- The evaluation table of a code: `evT(j, ⟨m, c⟩) = ev(c, j)`; variables `0 = j`,
`1 = ⟨m, c⟩`. -/
abbrev evT : PTm 2 := LeanProofs.IPRA.Combinatorics.LegendreDigits.dB

theorem evT_at (j m c : PTm n) : Γ ⊢[PRAAx] inst2 evT j (pairT m c) ≐ dg m j c :=
  LeanProofs.IPRA.Combinatorics.LegendreDigits.dB_at j m c

/-- The entry `evT(j, ⟨m, c⟩) mod m` of the evaluation table of `c` is the digit `ev(c, j)`. -/
theorem entry_dB {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (j c : PTm n) :
    Γ ⊢[PRAAx] rem (inst2 evT j (pairT m c)) m ≐ dg m j c :=
  (congrAp2 remF (evT_at j m c) (.eqRefl _)).eqTrans (rem_of_lt hm (rem_lt'' hm _))

private theorem recon_step {N m c : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (ih : Γ ⊢[PRAAx] code evT N m (pairT m c) + quo c (pw m N) * pw m N ≐ c) :
    Γ ⊢[PRAAx] code evT (succ N) m (pairT m c) + quo c (pw m (succ N)) * pw m (succ N) ≐ c := by
  ipra_lc natEq (code_succ (Γ := Γ) evT N m (pairT m c)) + 𝔞 (pw m N) * natEq (entry_dB hm N c) +
    𝔞 (quo c (pw m (succ N))) * natEq (pw_succ (Γ := Γ) m N) + natEq ih - 𝔞 (pw m N) * natEq (digit_step hm c N)

/-- Variables: `0 = N`, `1 = m`, `2 = c`. -/
private abbrev reconF : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (ap2 (sumF (cB evT)) (var 0) (pairT (var 1) (pairT (var 1) (var 2))) +
      quo (var 2) (pw (var 1) (var 0)) * pw (var 1) (var 0) ≐ var 2)

private theorem recon₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] reconF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    ipra_lc natEq (code_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) evT (var 0) (pairT (var 0) (var 1))) +
      𝔞 (quo (var 1 : PTm 2) (pw (var 0) zero)) * natEq (pw_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) (var 0)) +
      natEq ((congrAp2 quoF (.eqRefl (var 1 : PTm 2)) (pw_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) (var 0))).eqTrans (Prf.andE₁ (dmu (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) (K := one) (q := var 1) (r := zero) (pos_of_eq_succ (c := zero) (.eqRefl _)) (by ipra_ring) (le_refl one))))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (recon_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- Reconstruction from digits: `∑_{j<N} ev(c, j) m^j + ⌊c / m^N⌋ m^N = c`. -/
theorem recon {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N c : PTm n) :
    Γ ⊢[PRAAx] code evT N m (pairT m c) + quo c (pw m N) * pw m N ≐ c := by
  have h := inst (Γ := Γ) recon₀ (![N, m, c] : Fin 3 → PTm n)
  simp at h
  exact .impE h hm

/-- The second inverse law: for `c < m^N`, the code of the evaluation table of `c` is `c`. -/
theorem curry_ev {N m c : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hc : Γ ⊢[PRAAx] lt c (pw m N)) : Γ ⊢[PRAAx] code evT N m (pairT m c) ≐ c := by
  ipra_lc natEq (recon hm N c) - 𝔞 (pw m N) * natEq (quo_small (pw_pos' hm N) hc)

/-- The first inverse law as a closed sentence, for every table term `t`. Variables: `0 = N`,
`1 = j`, `2 = m`, `3 = p`. -/
theorem ev_curry_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((var 2 ≐ succ (pred (var 2))) ⟶ lt (var 1) (var 0) ⟶
      (dg (var 2) (var 1) (code t (var 0) (var 2) (var 3)) ≐
        rem (inst2 t (var 1) (var 3)) (var 2))) :=
  closeUniv 4 (.impI (.impI (ev_curry t Prf.hyp1 Prf.hyp0 _)))

/-- The second inverse law as a closed sentence. Variables: `0 = N`, `1 = m`, `2 = c`. -/
theorem curry_ev_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((var 1 ≐ succ (pred (var 1))) ⟶ lt (var 2) (pw (var 1) (var 0)) ⟶
      (code evT (var 0) (var 1) (pairT (var 1) (var 2)) ≐ var 2)) :=
  closeUniv 3 (.impI (.impI (curry_ev Prf.hyp1 Prf.hyp0)))

/-! ## The binary product `[n] × [m] ≅ [nm]` -/

/-- `i m + j < n m` for `i < n` and `j < m`. -/
theorem pair_lt {i j N m : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] lt (i * m + j) (N * m) := by
  refine le_of_eq_add (d := monus N (succ i) * m + monus m (succ j)) ?_
  ipra_lc 𝔞 m * natEq (eq_add_of_le hi) + natEq (eq_add_of_le hj)

/-- The first projection of a pair. -/
theorem pair_fst {i j m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] quo (i * m + j) m ≐ i := Prf.andE₁ (qr_block hm hj)

/-- The second projection of a pair. -/
theorem pair_snd {i j m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] rem (i * m + j) m ≐ j := Prf.andE₂ (qr_block hm hj)

/-- Every `k` is the pair of its projections. -/
theorem pair_eta {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] k ≐ quo k m * m + rem k m := div_eq' hm

/-- The second projection is below `m`. -/
theorem snd_lt {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] lt (rem k m) m := rem_lt'' hm k

private theorem fst_aux {k N m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hk : Γ ⊢[PRAAx] lt k (N * m)) (hq : Γ ⊢[PRAAx] le N (quo k m)) :
    Γ ⊢[PRAAx] le (succ k) k := by
  refine le_of_eq_add (d := monus (N * m) (succ k) + monus (quo k m) N * m + rem k m) ?_
  ipra_lc natEq (eq_add_of_le hk) + 𝔞 m * natEq (eq_add_of_le hq) + natEq (div_eq' (t := k) hm)

/-- The first projection of `k < n m` is below `n`. -/
theorem fst_lt {k N m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hk : Γ ⊢[PRAAx] lt k (N * m)) : Γ ⊢[PRAAx] lt (quo k m) N := by
  refine .orE (lt_or_le (quo k m) N) Prf.hyp0 ?_
  exact not_succ_le_self k _ (fst_aux hm.wk hk.wk Prf.hyp0)

end LeanProofs.IPRA.Foundations.FiniteSetExponential
