import IPRADerivations.DiophantineNumberTheory.DigitCode
import IPRADerivations.DiophantineNumberTheory.GcdUnique
import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Bounded-height enumeration for natural coordinates

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:northcott` ("Bounded-height
enumeration"), for vectors of length `N` with natural entries below `b` (the box `[0, B]^N`, `b = B + 1`):
"Visit each vector in ... a fixed lexicographic order. Retain it exactly when its gcd is one ... There are
precisely `(2B+1)^{n+1}` visits ... an explicit numerical implementation uses a visit counter with base
`(2B + 1)` digits ... Uniqueness is Lemma `lem:normalize`."

The visits are the codes `e < b^N` (`DigitCode`), the vector of a code is its digit vector
`LegendreDigits.dB`, and the retained codes are those whose digit vector has gcd `1` (`GcdList.gv`).
The output list is the rank/select enumeration of `Foundations/FilteredEnumeration`: its `r`-th element is
`sel K r (b^N) ⟨b, N⟩`, its length is `ℓ = rank K (b^N) ⟨b, N⟩ ≤ b^N`.

* `gv_congr`: pointwise-equal vectors have equal gcds;
* `kB`, `kB_at`: the filter;
* `north_sound`: every listed code is below `b^N` and its digit vector has gcd `1`;
* `north_complete`: every vector with entries below `b` and gcd `1` is the digit vector of a listed code;
* `north_inj`: the list is duplicate-free;
* `north_point`: the normalization of any nonzero vector in the box is listed (with `GcdNormalize`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.NorthcottNatural

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv gv_zero gv_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (congrGcd qBody q_le gv_quotients)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (code entriesLt code_lt digits_of_code)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne pw_pos')

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The digit vector, `LegendreDigits.dB`. -/
abbrev digB : PTm 2 := LeanProofs.IPRA.Combinatorics.LegendreDigits.dB

/-- Pointwise-equal vectors have equal gcds for every prefix of length at most `N`. -/
theorem gv_congr_all (f g : PTm 2) {N x y : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ inst2 g (var 0) (Syn.shift y))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ gv g (var 0) (Syn.shift y)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI ((gv_zero f x).eqTrans (gv_zero g y).eqSymm)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    let Δ := le (succ (var 0)) (Syn.shift N) ::
      (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ gv g (var 0) (Syn.shift y)) :: Γ.map Fm.shift
    have hle : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
    have ih : Δ ⊢[PRAAx] gv f (var 0) (Syn.shift x) ≐ gv g (var 0) (Syn.shift y) := Prf.impE Prf.hyp1 hle
    have hf : Δ ⊢[PRAAx] inst2 f (var 0) (Syn.shift x) ≐ inst2 g (var 0) (Syn.shift y) :=
      Prf.impE h.allOpen.wk.wk Prf.hyp0
    exact (gv_succ f (var 0) (Syn.shift x)).eqTrans ((congrGcd ih hf).eqTrans (gv_succ g (var 0) (Syn.shift y)).eqSymm)

/-- Pointwise-equal vectors have equal gcds. -/
theorem gv_congr (f g : PTm 2) {N x y : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ inst2 g (var 0) (Syn.shift y))) :
    Γ ⊢[PRAAx] gv f N x ≐ gv g N y := by
  have h2 := Prf.allE N (gv_congr_all f g h)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact Prf.impE h2 (le_refl N)

alias congrEqb := Common.congrEqb

/-- The filter: the digit vector of `e` (variable `0`) has gcd `1`, over `1 = ⟨b, N⟩`. -/
abbrev kB : PTm 2 := eqb (gv digB (sndT (var 1)) (pairT (fstT (var 1)) (var 0))) one

theorem kB_at (e b N : PTm k) : Γ ⊢[PRAAx] inst2 kB e (pairT b N) ≐ eqb (gv digB N (pairT b e)) one := by
  have h : inst2 kB e (pairT b N) = eqb (gv digB (sndT (pairT b N)) (pairT (fstT (pairT b N)) e)) one := by
    rw [show inst2 kB e (pairT b N) = Syn.subst ![e, pairT b N] kB from rfl]
    simp
  rw [h]
  exact congrEqb (congrAp2 _ (snd_pair _ _) (congrPairT (fst_pair _ _) (.eqRefl _))) (.eqRefl _)

theorem kept_of {e b N : PTm k} (h : Γ ⊢[PRAAx] gv digB N (pairT b e) ≐ one) :
    Γ ⊢[PRAAx] neg (inst2 kB e (pairT b N) ≐ zero) :=
  .impI (succ_ne_zero' _ (((kB_at e b N).eqTrans (eqb_of_eq h)).wk.eqSymm.eqTrans Prf.hyp0))

theorem gcd_of_kept {e b N : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 kB e (pairT b N) ≐ zero)) :
    Γ ⊢[PRAAx] gv digB N (pairT b e) ≐ one :=
  eq_of_eqb_ne (.impI (Prf.impE h.wk ((kB_at e b N).wk.eqTrans Prf.hyp0)))

/-- Every listed code is a visit `e < b^N` whose digit vector has gcd `1`. -/
theorem north_sound {b N r : PTm k} (hr : Γ ⊢[PRAAx] lt r (rank kB (pw b N) (pairT b N))) :
    Γ ⊢[PRAAx] lt (sel kB r (pw b N) (pairT b N)) (pw b N) ⋏
      (gv digB N (pairT b (sel kB r (pw b N) (pairT b N))) ≐ one) := by
  have s := sel_spec kB hr
  exact .andI (Prf.andE₁ s) (gcd_of_kept (Prf.andE₁ (Prf.andE₂ s)))

/-- The list is duplicate-free. -/
theorem north_inj {b N r r' : PTm k} (hr : Γ ⊢[PRAAx] lt r (rank kB (pw b N) (pairT b N)))
    (hr' : Γ ⊢[PRAAx] lt r' (rank kB (pw b N) (pairT b N)))
    (h : Γ ⊢[PRAAx] sel kB r (pw b N) (pairT b N) ≐ sel kB r' (pw b N) (pairT b N)) : Γ ⊢[PRAAx] r ≐ r' :=
  (Prf.andE₂ (Prf.andE₂ (sel_spec kB hr))).eqSymm.eqTrans
    ((congrAp2 _ h (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (sel_spec kB hr'))))

/-- Every vector with entries below `b` and gcd `1` is the digit vector of a listed code: its code `e` has
rank `< ℓ` and `sel (rank e) = e`. -/
theorem north_complete {V : PTm 2} {b x N : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hV : Γ ⊢[PRAAx] entriesLt V b x N) (hg : Γ ⊢[PRAAx] gv V N x ≐ one) :
    Γ ⊢[PRAAx] lt (rank kB (code V b x N) (pairT b N)) (rank kB (pw b N) (pairT b N)) ⋏
      (sel kB (rank kB (code V b x N) (pairT b N)) (pw b N) (pairT b N) ≐ code V b x N) := by
  have hlt := code_lt hV (le_refl N)
  have hk := kept_of (gv_congr digB V (digits_of_code hb hV) |>.eqTrans hg)
  exact .andI (rank_lt_size kB hlt hk) (sel_rank kB hlt hk)

/-- The normalization of a nonzero vector with entries below `b` is listed. -/
theorem north_point {f : PTm 2} {b x N : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hf : Γ ⊢[PRAAx] entriesLt f b x N) (hG : Γ ⊢[PRAAx] gv f N x ≐ succ (pred (gv f N x))) :
    Γ ⊢[PRAAx] lt (rank kB (code (qBody f) b (pairT N x) N) (pairT b N)) (rank kB (pw b N) (pairT b N)) ⋏
      (sel kB (rank kB (code (qBody f) b (pairT N x) N) (pairT b N)) (pw b N) (pairT b N) ≐
        code (qBody f) b (pairT N x) N) := by
  have hq : Γ ⊢[PRAAx] entriesLt (qBody f) b (pairT N x) N := by
    refine .allI (.impI ?_)
    have hGs : Γ.map Fm.shift ⊢[PRAAx] gv f (Syn.shift N) (Syn.shift x) ≐ succ (pred (gv f (Syn.shift N) (Syn.shift x))) := by
      have e := hG.shift; simpa [Fm.shift, Syn.shift] using e
    have l := q_le f hGs.wk (Prf.hyp0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    have u := Prf.impE hf.allOpen.wk Prf.hyp0
    have e : Syn.shift (pairT N x) = pairT (Syn.shift N) (Syn.shift x) := by simp [Syn.shift]
    rw [e]
    exact lt_of_le_of_lt l u
  exact north_complete hb hq (gv_quotients f hG)

end LeanProofs.IPRA.DiophantineNumberTheory.NorthcottNatural
