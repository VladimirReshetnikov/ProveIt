import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Combinatorics.LegendreDigits

/-!
# Mixed-radix expansion of a number

Packet: `foundations/FINER-iPRA-framework-2026-11-16`, `paper/sections/03_finite_data.tex`, the lemma
"Mixed-radix correctness", second half: "if `c < R`, then re-encoding its decoded digits gives `c`". The same
statement is the surjectivity half of the packed codes of `foundations/STRIVE-iPRA-framework-2026-11-16`.

The radices are a body `r(i, y)` and the number is the first component `c = fst y` of the parameter, so that
the decoded digit `dg_i = (c div Pl i) mod r_i` is a body over `(i, y)`; radices that do not depend on `c`
read `snd y`. With `Pl k = ∏_{j<k} r_j` and `Cd k = ∑_{i<k} dg_i · Pl i` (the code of
`Foundations/MixedRadix` for the decoded digits), and radices `r_j ≥ 1` for `j < m`:

* `expansion`: `Cd k + Pl k · (c div Pl k) = c` for every `k ≤ m` (the paper's repeated quotient-remainder
  equation, with the current quotient `c div Pl k`);
* `pl_pos`: `0 < Pl k` for `k ≤ m`;
* `digits_bounded`: `dg_j < r_j` for `j < m`, so the decoded digits form a bounded digit vector, to which
  `MixedRadix.code_lt` and `MixedRadix.decode` apply;
* `reencode`: if `c < Pl m`, then `Cd m = c`.

The step uses `LegendreDigits.quo_quo`, `(c div P) div r = c div (P r)`.

Two further statements of the STRIVE packet (`paper/sections/04_mixed_radix.tex`) are recorded here:

* `append_interval` (the lemma "Append interval"): `x < P` and `d < B` give `x + d P < P B`;
* `code_ext` (the corollary "Code extensionality", forward direction): bounded digit vectors with equal
  codes have equal digits.
-/

namespace LeanProofs.IPRA.Foundations.MixedRadixExpansion

open_ipra exports
open LeanProofs.IPRA.Foundations.MixedRadix
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm quo_quo quo_small pos_mul')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The decoded digit `dg_i = (c div Pl i) mod r_i` of `c = fst y`, over `0 = i`, `1 = y`. -/
abbrev dgB (r : PTm 2) : PTm 2 := rem (quo (fstT (var 1)) (ap2 (prodF r) (var 0) (var 1))) r

theorem inst2_dgB (r : PTm 2) (i y : PTm n) :
    inst2 (dgB r) i y = rem (quo (fstT y) (ap2 (prodF r) i y)) (inst2 r i y) := by
  simp [inst2]

theorem lt_of_pos {b c : PTm n} (h : Γ ⊢[PRAAx] b ≐ succ c) : Γ ⊢[PRAAx] lt zero b :=
  Order.zero_lt_of_eq_succ h

/-! ## The quotient-remainder expansion -/

theorem exp_base (r : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] Cd r (dgB r) zero y + Pl r zero y * quo (fstT y) (Pl r zero y) ≐ fstT y := by
  have pz := prod_zero (Γ := Γ) r y
  have u := div_mod_unique (Γ := Γ) (z := fstT y) (q := fstT y) (r := zero) (K' := zero)
    (by ipra_ring) (zero_lt_succ zero)
  have q := natEq ((congrAp2 quoF (.eqRefl (fstT y)) pz).eqTrans (Prf.andE₁ u))
  have z := natEq (sum_zero (Γ := Γ) (dP r (dgB r)) y)
  have p := natEq pz
  apply deriveNat; ipra_simps
  rw [z, p, q]; ring

theorem exp_step {r : PTm 2} {k y : PTm n}
    (hP : Γ ⊢[PRAAx] Pl r k y ≐ succ (pred (Pl r k y)))
    (hR : Γ ⊢[PRAAx] inst2 r k y ≐ succ (pred (inst2 r k y)))
    (ih : Γ ⊢[PRAAx] Cd r (dgB r) k y + Pl r k y * quo (fstT y) (Pl r k y) ≐ fstT y) :
    Γ ⊢[PRAAx] Cd r (dgB r) (succ k) y + Pl r (succ k) y * quo (fstT y) (Pl r (succ k) y) ≐ fstT y := by
  have es' := sum_succ' (Γ := Γ) (dP r (dgB r)) k y
  rw [inst2_dP, inst2_dgB] at es'
  have es := natEq es'
  have ep' := prod_succ' (Γ := Γ) r k y
  have ep := natEq ep'
  have eq := natEq ((congrAp2 quoF (.eqRefl (fstT y)) ep').eqTrans (quo_quo hP hR (fstT y)).eqSymm)
  have e₂ := natEq (Prf.andE₁ (dm hR (quo (fstT y) (Pl r k y))))
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [es, ep, eq]; linear_combination i - 𝔟 (Pl r k y) * e₂

/-- One step of the invariant `0 < Pl k ∧ Cd k + Pl k · (c div Pl k) = c`, guarded by `k ≤ m`. -/
theorem inv_step {r : PTm 2} {k y m : PTm n} (hk : Γ ⊢[PRAAx] le (succ k) m)
    (hr : Γ ⊢[PRAAx] lt zero (inst2 r k y))
    (ih : Γ ⊢[PRAAx] le k m ⟶
      (lt zero (Pl r k y) ⋏ (Cd r (dgB r) k y + Pl r k y * quo (fstT y) (Pl r k y) ≐ fstT y))) :
    Γ ⊢[PRAAx] lt zero (Pl r (succ k) y) ⋏
      (Cd r (dgB r) (succ k) y + Pl r (succ k) y * quo (fstT y) (Pl r (succ k) y) ≐ fstT y) := by
  have ih' := Prf.impE ih (le_trans (le_succ_self k) hk)
  have hR := pos_of_lt hr
  have hP := pos_of_lt (Prf.andE₁ ih')
  exact .andI (lt_of_pos ((prod_succ' r k y).eqTrans (pos_mul' hP hR))) (exp_step hP hR (Prf.andE₂ ih'))

section expansion

variable {r : PTm 2} {y m : PTm n}

theorem exp_all
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift m) ⟶
      (lt zero (Pl r (var 0) (Syn.shift y)) ⋏
        (Cd r (dgB r) (var 0) (Syn.shift y) +
            Pl r (var 0) (Syn.shift y) * quo (fstT (Syn.shift y)) (Pl r (var 0) (Syn.shift y)) ≐
          fstT (Syn.shift y)))) := by
  refine PRA.qfInd _ ⟨le_QF _ _, lt_QF _ _, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_fstT,
      PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero]
    exact .impI (.andI (lt_of_pos (prod_zero r y)) (exp_base r y))
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_fstT,
      PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_step Prf.hyp0 (Prf.impE hpos.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

theorem exp_at
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y))))
    {k : PTm n} (hk : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] lt zero (Pl r k y) ⋏
      (Cd r (dgB r) k y + Pl r k y * quo (fstT y) (Pl r k y) ≐ fstT y) := by
  have h := Prf.allE k (exp_all hpos)
  simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_fstT,
    PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at h
  exact .impE h hk

/-- The repeated quotient-remainder equation: `Cd k + Pl k · (c div Pl k) = c` for `k ≤ m`. -/
theorem expansion
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y))))
    {k : PTm n} (hk : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] Cd r (dgB r) k y + Pl r k y * quo (fstT y) (Pl r k y) ≐ fstT y :=
  Prf.andE₂ (exp_at hpos hk)

/-- The place values are positive. -/
theorem pl_pos
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y))))
    {k : PTm n} (hk : Γ ⊢[PRAAx] le k m) : Γ ⊢[PRAAx] lt zero (Pl r k y) :=
  Prf.andE₁ (exp_at hpos hk)

/-- The decoded digits are below their radices. -/
theorem digits_bounded
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      lt (inst2 (dgB r) (var 0) (Syn.shift y)) (inst2 r (var 0) (Syn.shift y))) := by
  refine .allI (.impI ?_)
  rw [inst2_dgB]
  exact Prf.andE₂ (dm (pos_of_lt (Prf.impE hpos.allOpen.wk Prf.hyp0)) _)

/-- "Mixed-radix correctness", converse: a number `c < Pl m` is the code of its decoded digits. -/
theorem reencode
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 r (var 0) (Syn.shift y))))
    (hc : Γ ⊢[PRAAx] lt (fstT y) (Pl r m y)) : Γ ⊢[PRAAx] Cd r (dgB r) m y ≐ fstT y := by
  have e := natEq (expansion hpos (le_refl m))
  have qs := natEq (quo_small (pos_of_lt hc) hc)
  apply deriveNat; ipra_simps
  rw [qs] at e; linear_combination e

end expansion

/-! ## The append interval and code extensionality -/

/-- "Append interval": `x < P` and `d < B` give `x + d P < P B`. -/
theorem append_interval {x P d B : PTm n} (hx : Γ ⊢[PRAAx] lt x P) (hd : Γ ⊢[PRAAx] lt d B) :
    Γ ⊢[PRAAx] lt (x + d * P) (P * B) :=
  lt_congr (add_comm _ _) (mul_comm _ _) (Order.mul_add_lt_mul hd hx)

/-- "Code extensionality": two digit vectors below the radices with the same code agree at every index. -/
theorem code_ext {r d d' : PTm 2} {x i t : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x))))
    (hb' : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d' (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x))))
    (e : Γ ⊢[PRAAx] Cd r d (succ i + t) x ≐ Cd r d' (succ i + t) x) :
    Γ ⊢[PRAAx] inst2 d i x ≐ inst2 d' i x :=
  (decode hb).eqSymm.eqTrans
    ((congrAp2 remF (congrAp2 quoF e (.eqRefl _)) (.eqRefl _)).eqTrans (decode hb'))

end LeanProofs.IPRA.Foundations.MixedRadixExpansion
