import IPRADerivations.DiophantineNumberTheory.NorthcottNatural
import IPRADerivations.Core.Header

/-!
# Bounded-height enumeration on a decidable locus

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:northcott`, the filter by the
equations: "Retain it exactly when its gcd is one, its first nonzero entry is positive, and all polynomial values
vanish", and Corollary `cor:heightbound` ("suppose an integer `B` and a proof of `P ∈ V(ℚ) ⇒ Ht(P) ≤ B` are
supplied. Then `L(n, B, V)` is the complete rational-point list"), for natural coordinates.

The locus is any primitive recursive test `T(e, q)` on the visit code `e` with parameters `q` (for the
polynomial system: the vanishing of the values at the digit vector of `e`); a code is retained when the gcd of
its digit vector is `1` and `T(e, q) = 0`.

* `kL_at`, `kept_of`, `gcd_of_kept`, `test_of_kept`: the filter;
* `locus_sound`: every listed code is a visit `e < b^N` with primitive digit vector and `T(e, q) = 0`;
* `locus_inj`: the list is duplicate-free;
* `locus_complete`: every primitive vector with entries below `b` whose code passes `T` is listed. With
  `b = B + 1`, the hypothesis that every entry is below `b` is the supplied height bound of
  `cor:heightbound`, so the list is then complete for the locus.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.NorthcottLocus

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (code entriesLt code_lt code_digit)
open LeanProofs.IPRA.DiophantineNumberTheory.NorthcottNatural (digB gv_congr congrEqb)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dB_at)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The filter over `0 = e`, `1 = ⟨⟨b, N⟩, q⟩`: primitive digit vector and `T(e, q) = 0`. -/
abbrev kL (T : PTm 2) : PTm 2 :=
  eqb (gv digB (sndT (fstT (var 1))) (pairT (fstT (fstT (var 1))) (var 0))) one * eqb (inst2 T (var 0) (sndT (var 1))) zero

/-- The parameter `⟨⟨b, N⟩, q⟩`. -/
abbrev prm (b N q : PTm k) : PTm k := pairT (pairT b N) q

theorem kL_at (T : PTm 2) (e b N q : PTm k) :
    Γ ⊢[PRAAx] inst2 (kL T) e (prm b N q) ≐ eqb (gv digB N (pairT b e)) one * eqb (inst2 T e q) zero := by
  have h : inst2 (kL T) e (prm b N q) =
      eqb (gv digB (sndT (fstT (prm b N q))) (pairT (fstT (fstT (prm b N q))) e)) one *
        eqb (inst2 T e (sndT (prm b N q))) zero := by
    rw [show inst2 (kL T) e (prm b N q) = Syn.subst ![e, prm b N q] (kL T) from rfl]
    simp
  rw [h]
  have e1 : Γ ⊢[PRAAx] sndT (fstT (prm b N q)) ≐ N := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have e2 : Γ ⊢[PRAAx] fstT (fstT (prm b N q)) ≐ b := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  exact congrMul (congrEqb (congrAp2 _ e1 (congrPairT e2 (.eqRefl _))) (.eqRefl _))
    (congrEqb (congrInst2 T (.eqRefl _) (snd_pair _ _)) (.eqRefl _))

theorem kept_of (T : PTm 2) {e b N q : PTm k} (hg : Γ ⊢[PRAAx] gv digB N (pairT b e) ≐ one)
    (ht : Γ ⊢[PRAAx] inst2 T e q ≐ zero) : Γ ⊢[PRAAx] neg (inst2 (kL T) e (prm b N q) ≐ zero) := by
  have v : Γ ⊢[PRAAx] inst2 (kL T) e (prm b N q) ≐ one :=
    (kL_at T e b N q).eqTrans ((congrMul (eqb_of_eq hg) (eqb_of_eq ht)).eqTrans (by ipra_ring))
  exact .impI (succ_ne_zero' _ (v.wk.eqSymm.eqTrans Prf.hyp0))

theorem factors_of_kept (T : PTm 2) {e b N q : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 (kL T) e (prm b N q) ≐ zero)) :
    Γ ⊢[PRAAx] neg (eqb (gv digB N (pairT b e)) one ≐ zero) ⋏ neg (eqb (inst2 T e q) zero ≐ zero) := by
  have k := kL_at (Γ := Γ) T e b N q
  refine .andI (.impI ?_) (.impI ?_)
  · exact Prf.impE h.wk (k.wk.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))
  · exact Prf.impE h.wk (k.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

/-- Every listed code is a visit with primitive digit vector on the locus. -/
theorem locus_sound (T : PTm 2) {b N q r : PTm k}
    (hr : Γ ⊢[PRAAx] lt r (rank (kL T) (pw b N) (prm b N q))) :
    Γ ⊢[PRAAx] lt (sel (kL T) r (pw b N) (prm b N q)) (pw b N) ⋏
      ((gv digB N (pairT b (sel (kL T) r (pw b N) (prm b N q))) ≐ one) ⋏
        (inst2 T (sel (kL T) r (pw b N) (prm b N q)) q ≐ zero)) := by
  have s := sel_spec (kL T) hr
  have f := factors_of_kept T (Prf.andE₁ (Prf.andE₂ s))
  exact .andI (Prf.andE₁ s) (.andI (eq_of_eqb_ne (Prf.andE₁ f)) (eq_of_eqb_ne (Prf.andE₂ f)))

/-- The list is duplicate-free. -/
theorem locus_inj (T : PTm 2) {b N q r r' : PTm k}
    (hr : Γ ⊢[PRAAx] lt r (rank (kL T) (pw b N) (prm b N q)))
    (hr' : Γ ⊢[PRAAx] lt r' (rank (kL T) (pw b N) (prm b N q)))
    (h : Γ ⊢[PRAAx] sel (kL T) r (pw b N) (prm b N q) ≐ sel (kL T) r' (pw b N) (prm b N q)) : Γ ⊢[PRAAx] r ≐ r' :=
  (Prf.andE₂ (Prf.andE₂ (sel_spec (kL T) hr))).eqSymm.eqTrans
    ((congrAp2 _ h (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (sel_spec (kL T) hr'))))

/-- Completeness under the supplied height bound: every primitive vector with entries below `b` whose code
lies on the locus is listed. -/
theorem locus_complete (T : PTm 2) {V : PTm 2} {b x N q : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hV : Γ ⊢[PRAAx] entriesLt V b x N) (hg : Γ ⊢[PRAAx] gv V N x ≐ one)
    (ht : Γ ⊢[PRAAx] inst2 T (code V b x N) q ≐ zero) :
    Γ ⊢[PRAAx] lt (rank (kL T) (code V b x N) (prm b N q)) (rank (kL T) (pw b N) (prm b N q)) ⋏
      (sel (kL T) (rank (kL T) (code V b x N) (prm b N q)) (pw b N) (prm b N q) ≐ code V b x N) := by
  have hlt := code_lt hV (le_refl N)
  have hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 digB (var 0) (Syn.shift (pairT b (code V b x N))) ≐ inst2 V (var 0) (Syn.shift x)) := by
    refine .allI (.impI ?_)
    have hbs : Γ.map Fm.shift ⊢[PRAAx] Syn.shift b ≐ succ (pred (Syn.shift b)) := by
      have e := hb.shift; simpa [Fm.shift, Syn.shift] using e
    have hVs : Γ.map Fm.shift ⊢[PRAAx] entriesLt V (Syn.shift b) (Syn.shift x) (Syn.shift N) := by
      have e := hV.shift
      simpa [Fm.shift, Syn.shift, entriesLt, Syn.subst_subst, Syn.up_succ, Syn.up_zero, Syn.shift_var] using e
    have c := code_digit hbs.wk hVs.wk (Prf.hyp0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    have e : Syn.shift (pairT b (code V b x N)) =
        pairT (Syn.shift b) (code V (Syn.shift b) (Syn.shift x) (Syn.shift N)) := by
      simp [Syn.shift]
    rw [e]
    exact (dB_at _ _ _).eqTrans c
  have hk := kept_of T (q := q) (gv_congr digB V hd |>.eqTrans hg) ht
  exact .andI (rank_lt_size (kL T) hlt hk) (sel_rank (kL T) hlt hk)

end LeanProofs.IPRA.DiophantineNumberTheory.NorthcottLocus
