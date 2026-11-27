import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums

/-!
# Base-`b` codes of vectors

The visit counter of `diophantine_geometry_ipra`, Theorem `thm:northcott` ("an explicit numerical
implementation uses a visit counter with base `(2B + 1)` digits of length `n + 1`"): a vector `v_0, …, v_{N−1}`
with entries `v_i < b` is coded by `E = ∑_{i<N} v_i b^i`, and its digits `⌊E/b^j⌋ mod b` return the entries.

* `cB_at`, `code_succ`: `E(M + 1) = E(M) + v_M b^M`;
* `code_lt`: `E(M) < b^M` for `M ≤ N`;
* `code_digit`: the `j`-th digit of `E(N)` is `v_j` for `j < N`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.DigitCode

open_ipra exports
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dB dB_at dm dmu)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `v_i b^i`, over `0 = i`, `1 = ⟨b, x⟩`. -/
abbrev cB (V : PTm 2) : PTm 2 := inst2 V (var 0) (sndT (var 1)) * pw (fstT (var 1)) (var 0)

/-- `E(M) = ∑_{i<M} v_i b^i`. -/
abbrev code (V : PTm 2) (b x M : PTm k) : PTm k := ap2 (sumF (cB V)) M (pairT b x)

theorem cB_at (V : PTm 2) (i b x : PTm k) :
    Γ ⊢[PRAAx] inst2 (cB V) i (pairT b x) ≐ inst2 V i x * pw b i := by
  have h : inst2 (cB V) i (pairT b x) = inst2 V i (sndT (pairT b x)) * pw (fstT (pairT b x)) i := by
    rw [show inst2 (cB V) i (pairT b x) = Syn.subst ![i, pairT b x] (cB V) from rfl]
    simp
  rw [h]
  exact congrMul (congrInst2 V (.eqRefl _) (snd_pair _ _)) (congrPw (fst_pair _ _) (.eqRefl _))

theorem code_succ (V : PTm 2) (b x M : PTm k) :
    Γ ⊢[PRAAx] code V b x (succ M) ≐ code V b x M + inst2 V M x * pw b M :=
  (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (cB_at V M b x))

theorem congrCode (V : PTm 2) {b x M M' : PTm k} (h : Γ ⊢[PRAAx] M ≐ M') :
    Γ ⊢[PRAAx] code V b x M ≐ code V b x M' := congrAp2 _ h (.eqRefl _)

/-- The entries are digits: `v_i < b` for `i < N`. -/
abbrev entriesLt (V : PTm 2) (b x N : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ lt (inst2 V (var 0) (Syn.shift x)) (Syn.shift b))

theorem entry_lt {V : PTm 2} {b x N i : PTm k} (h : Γ ⊢[PRAAx] entriesLt V b x N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (inst2 V i x) b := by
  have h2 := Prf.allE i h
  simp only [Fm.subst_imp, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact Prf.impE h2 hi

/-- `E(M) < b^M` for `M ≤ N`. -/
theorem code_lt {V : PTm 2} {b x N M : PTm k} (hV : Γ ⊢[PRAAx] entriesLt V b x N) (hM : Γ ⊢[PRAAx] le M N) :
    Γ ⊢[PRAAx] lt (code V b x M) (pw b M) := by
  let P : Fm PTm (k + 1) :=
    lt (code V (Syn.shift b) (Syn.shift x) (var 0)) (pw (Syn.shift b) (var 0))
  have atIndex : Γ ⊢[PRAAx] P.subst (Syn.inst M) := by
    refine qfIndAtMost hM (le_QF _ _) ?_ ?_
    · simp only [P, subst_lt, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have z := natEq (sum_zero (Γ := Γ) (cB V) (pairT b x))
      have p := natEq (pw_zero (Γ := Γ) b)
      ipra_le 0 using linear_combination p - z
    · simp only [P, subst_lt, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] P := Prf.hyp1
      have hv : Δ ⊢[PRAAx] le (succ (inst2 V (var 0) (Syn.shift x))) (Syn.shift b) :=
        .impE hV.allOpen.wk.wk Prf.hyp0
      have c := natEq (code_succ (Γ := Δ) V (Syn.shift b) (Syn.shift x) (var 0))
      have p := natEq (pw_succ (Γ := Δ) (Syn.shift b) (var 0))
      show Δ ⊢[PRAAx] le (succ (code V (Syn.shift b) (Syn.shift x) (succ (var 0)))) (pw (Syn.shift b) (succ (var 0)))
      ipra_le sl ih + 𝔞 (pw (Syn.shift b) (var 0)) * sl hv using linear_combination p - c
  simpa only [P, subst_lt, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atIndex

/-- `z mod b = z` for `z < b`. -/
theorem rem_small {b z : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (h : Γ ⊢[PRAAx] lt z b) :
    Γ ⊢[PRAAx] rem z b ≐ z :=
  Prf.andE₂ (dmu hb (q := zero) (r := z) (by ipra_ring) h)

/-- Adding a multiple of `b^{j+1}` does not change the `j`-th digit. -/
theorem digit_shift {b z c j : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] rem (quo (z + c * (pw b j * b)) (pw b j)) b ≐ rem (quo z (pw b j)) b := by
  have e : Γ ⊢[PRAAx] z + c * (pw b j * b) ≐ z + pw b j * (b * c) := by ipra_ring
  have q := (congrAp2 quoF e (.eqRefl (pw b j))).eqTrans
    (Prf.andE₁ (Division.div_mod_add_mul (pw_pos' hb j)))
  exact (congrAp2 remF q (.eqRefl _)).eqTrans (Prf.andE₂ (Division.div_mod_add_mul hb))

/-- `code_digit`: the `j`-th digit of `E(N)` is `v_j` for `j < N`. -/
theorem code_digit {V : PTm 2} {b x N j : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hV : Γ ⊢[PRAAx] entriesLt V b x N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] rem (quo (code V b x N) (pw b j)) b ≐ inst2 V j x := by
  -- the digit is fixed once `j` is coded, by induction on the number `D` of later entries
  have hall : Γ ⊢[PRAAx] Fm.all (le (succ (Syn.shift j) + var 0) (Syn.shift N) ⟶
      rem (quo (code V (Syn.shift b) (Syn.shift x) (succ (Syn.shift j) + var 0)) (pw (Syn.shift b) (Syn.shift j)))
        (Syn.shift b) ≐ inst2 V (Syn.shift j) (Syn.shift x)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · ipra_ind_simp [subst_le, subst_ap2, subst_inst2, subst_pairT, Syn.subst_inst_shift]
      refine .impI ?_
      let Δ := le (succ j + zero) N :: Γ
      have hjN : Δ ⊢[PRAAx] le j N := le_trans (le_succ_self _) ((le_congr (add_zero _) (.eqRefl _) Prf.hyp0))
      have hjN' : Δ ⊢[PRAAx] lt j N := le_congr (add_zero _) (.eqRefl _) Prf.hyp0
      have bl := code_lt hV.wk hjN
      have vj := entry_lt hV.wk hjN'
      have c := natEq ((congrCode (Γ := Δ) V (b := b) (x := x) (add_zero (succ j))).eqTrans (code_succ V b x j))
      have u := dmu (pw_pos' hb.wk j) (z := code V b x (succ j + zero)) (q := inst2 V j x) (r := code V b x j)
        (by ipra_lc c) bl
      exact (congrAp2 remF (Prf.andE₁ u) (.eqRefl _)).eqTrans (rem_small hb.wk vj)
    · ipra_ind_simp [subst_le, subst_ap2, subst_inst2, subst_pairT, subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (Syn.shift j) + succ (var 0)) (Syn.shift N) ::
        (le (succ (Syn.shift j) + var 0) (Syn.shift N) ⟶
          rem (quo (code V (Syn.shift b) (Syn.shift x) (succ (Syn.shift j) + var 0)) (pw (Syn.shift b) (Syn.shift j)))
            (Syn.shift b) ≐ inst2 V (Syn.shift j) (Syn.shift x)) :: Γ.map Fm.shift
      have hbs := Common.pos_shift hb
      have hb' : Δ ⊢[PRAAx] Syn.shift b ≐ succ (pred (Syn.shift b)) := hbs.wk.wk
      have hle : Δ ⊢[PRAAx] le (succ (Syn.shift j) + var 0) (Syn.shift N) :=
        le_trans (by ipra_le 1) Prf.hyp0
      have ih := Prf.impE Prf.hyp1 hle
      have eM : Δ ⊢[PRAAx] succ (Syn.shift j) + succ (var 0) ≐ succ (succ (Syn.shift j) + var 0) := by ipra_ring
      have c := (congrCode (Γ := Δ) V (b := Syn.shift b) (x := Syn.shift x) eM).eqTrans
        (code_succ V (Syn.shift b) (Syn.shift x) (succ (Syn.shift j) + var 0))
      have ep : Δ ⊢[PRAAx] pw (Syn.shift b) (succ (Syn.shift j) + var 0) ≐
          pw (Syn.shift b) (Syn.shift j) * (pw (Syn.shift b) (var 0) * Syn.shift b) := by
        have a := natEq (pw_add (Γ := Δ) (Syn.shift b) (Syn.shift j) (succ (var 0)))
        have s := natEq (pw_succ (Γ := Δ) (Syn.shift b) (var 0))
        have q : Δ ⊢[PRAAx] pw (Syn.shift b) (succ (Syn.shift j) + var 0) ≐
            pw (Syn.shift b) (Syn.shift j + succ (var 0)) := congrPw (.eqRefl _) (by ipra_ring)
        ipra_lc natEq q + a + 𝔞 (pw (Syn.shift b) (Syn.shift j)) * s
      have ec : Δ ⊢[PRAAx] code V (Syn.shift b) (Syn.shift x) (succ (Syn.shift j) + succ (var 0)) ≐
          code V (Syn.shift b) (Syn.shift x) (succ (Syn.shift j) + var 0) +
            (inst2 V (succ (Syn.shift j) + var 0) (Syn.shift x) * pw (Syn.shift b) (var 0)) *
              (pw (Syn.shift b) (Syn.shift j) * Syn.shift b) := by
        ipra_lc natEq c + 𝔞 (inst2 V (succ (Syn.shift j) + var 0) (Syn.shift x)) * natEq ep
      exact (congrAp2 remF (congrAp2 quoF ec (.eqRefl _)) (.eqRefl _)).eqTrans ((digit_shift hb').eqTrans ih)
  have h2 := Prf.allE (monus N (succ j)) hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_inst2, PTm.subst_add, subst_pairT,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at h2
  have eN : Γ ⊢[PRAAx] N ≐ succ j + monus N (succ j) := eq_add_of_le hj
  have r := Prf.impE h2 (le_congr eN (.eqRefl _) (le_refl N))
  exact (congrAp2 remF (congrAp2 quoF (congrCode V eN) (.eqRefl _)) (.eqRefl _)).eqTrans r

/-- Decoding a bounded digit vector's code recovers every entry in its prefix. -/
theorem digits_of_code {V : PTm 2} {b x N : PTm k}
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hV : Γ ⊢[PRAAx] entriesLt V b x N) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 dB (var 0) (Syn.shift (pairT b (code V b x N))) ≐ inst2 V (var 0) (Syn.shift x)) := by
  refine .allI (.impI ?_)
  have hbs := Common.pos_shift hb
  have hVs : Γ.map Fm.shift ⊢[PRAAx] entriesLt V (Syn.shift b) (Syn.shift x) (Syn.shift N) := by
    have e := hV.shift
    simpa [Fm.shift, Syn.shift, entriesLt, Syn.subst_subst, Syn.up_succ, Syn.up_zero, Syn.shift_var] using e
  have c := code_digit hbs.wk hVs.wk (Prf.hyp0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  have e : Syn.shift (pairT b (code V b x N)) = pairT (Syn.shift b) (code V (Syn.shift b) (Syn.shift x) (Syn.shift N)) := by
    simp [Syn.shift]
  rw [e]
  exact (dB_at _ _ _).eqTrans c

end LeanProofs.IPRA.DiophantineNumberTheory.DigitCode

export_ipra DiophantineNumberTheory.DigitCode (code_digit code_lt entriesLt)
