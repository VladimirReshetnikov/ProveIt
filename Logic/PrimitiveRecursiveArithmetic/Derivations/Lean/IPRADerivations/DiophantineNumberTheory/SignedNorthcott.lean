import IPRADerivations.DiophantineNumberTheory.SignedDigit

/-!
# Bounded-height enumeration with signed coordinates

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:northcott`: "Visit each vector in
`[−B, B]^{n+1}` in a fixed lexicographic order. Retain it exactly when its gcd is one, its first nonzero entry is
positive ... an explicit numerical implementation uses a visit counter with base `(2B + 1)` digits of length
`n + 1`; subtract `B` from each digit." Here without polynomial conditions (see `NorthcottLocus` for the filter).

Visits are the codes `e < (2B + 1)^N`; digit `j` of `e` decodes to a sign `sgnOf` and a magnitude `magOf`
(`SignedDigit`). A code is retained when the decoded magnitudes have gcd `1` and every decoded sign is at most
the gcd of the preceding magnitudes (the first nonzero entry is positive); the list is the rank/select
enumeration of `Foundations/FilteredEnumeration`.

* `gv_congr_all`: pointwise-equal vectors have equal prefix gcds;
* `kS_at`, `tS_at`: the filter, a product of the gcd test and the bounded test of the sign convention;
* `signed_sound`: every listed code decodes to a normalized signed vector;
* `signed_complete`: every normalized signed vector with magnitudes `≤ B` is the decoding of a listed code;
* `signed_inj`: the list is duplicate-free; with `SignedVector.signed_vector_unique` the listed points are
  pairwise distinct as projective points.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SignedNorthcott

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.SignedDigit (sgnOf magOf congrSg enc_dec enc_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv gv_zero gv_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (congrGcd)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (code entriesLt code_lt code_digit)
open LeanProofs.IPRA.DiophantineNumberTheory.NorthcottNatural (congrEqb gv_congr)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_intro all_reflect all_cases)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Pointwise-equal vectors have equal prefix gcds, for every prefix `M ≤ N`. -/
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
    have hle : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ gv g (var 0) (Syn.shift y)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hle
    have hf := Prf.impE h.allOpen.wk.wk (Prf.hyp0 : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ gv f (var 0) (Syn.shift x) ≐ gv g (var 0) (Syn.shift y)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    exact (gv_succ f (var 0) (Syn.shift x)).eqTrans ((congrGcd ih hf).eqTrans (gv_succ g (var 0) (Syn.shift y)).eqSymm)

/-- The base `2B + 1`. -/
abbrev bse (B : PTm k) : PTm k := succ (two * B)

/-- Digit `j` of `e`, over `0 = j`, `1 = ⟨B, e⟩`. -/
abbrev dgB : PTm 2 := rem (quo (sndT (var 1)) (pw (succ (two * fstT (var 1))) (var 0))) (succ (two * fstT (var 1)))
/-- The decoded sign. -/
abbrev sgB : PTm 2 := sgnOf (fstT (var 1)) dgB
/-- The decoded magnitude. -/
abbrev mgB : PTm 2 := magOf (fstT (var 1)) dgB

/-- The digit of `e` at `j`. -/
abbrev dig (B e j : PTm k) : PTm k := rem (quo e (pw (bse B) j)) (bse B)

theorem congrSgn {B B' d d' : PTm k} (hB : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] sgnOf B d ≐ sgnOf B' d' := congrSg (congrMonus hd hB)

theorem congrMag {B B' d d' : PTm k} (hB : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] magOf B d ≐ magOf B' d' := congrMonus hd (congrMul (congrSgn hB hd) hB)

theorem dg_eq (j B e : PTm k) : Γ ⊢[PRAAx] rem (quo (sndT (pairT B e)) (pw (succ (two * fstT (pairT B e))) j))
    (succ (two * fstT (pairT B e))) ≐ dig B e j := by
  have hb : Γ ⊢[PRAAx] succ (two * fstT (pairT B e)) ≐ bse B := congrSucc (congrMul (.eqRefl _) (fst_pair _ _))
  exact congrAp2 remF (congrAp2 quoF (snd_pair _ _) (congrPw hb (.eqRefl _))) hb

theorem sg_at (j B e : PTm k) : Γ ⊢[PRAAx] inst2 sgB j (pairT B e) ≐ sgnOf B (dig B e j) := by
  have h : inst2 sgB j (pairT B e) = sgnOf (fstT (pairT B e))
      (rem (quo (sndT (pairT B e)) (pw (succ (two * fstT (pairT B e))) j)) (succ (two * fstT (pairT B e)))) := by
    rw [show inst2 sgB j (pairT B e) = Syn.subst ![j, pairT B e] sgB from rfl]; simp
  rw [h]; exact congrSgn (fst_pair _ _) (dg_eq j B e)

theorem mg_at (j B e : PTm k) : Γ ⊢[PRAAx] inst2 mgB j (pairT B e) ≐ magOf B (dig B e j) := by
  have h : inst2 mgB j (pairT B e) = magOf (fstT (pairT B e))
      (rem (quo (sndT (pairT B e)) (pw (succ (two * fstT (pairT B e))) j)) (succ (two * fstT (pairT B e)))) := by
    rw [show inst2 mgB j (pairT B e) = Syn.subst ![j, pairT B e] mgB from rfl]; simp
  rw [h]; exact congrMag (fst_pair _ _) (dg_eq j B e)

/-- The sign test at `i`, over `1 = ⟨B, e⟩`: the sign is at most the gcd of the preceding magnitudes. -/
abbrev tS : PTm 2 := eqb (monus (inst2 sgB (var 0) (var 1)) (gv mgB (var 0) (var 1))) zero

/-- The filter over `0 = e`, `1 = ⟨B, N⟩`. -/
abbrev kS : PTm 2 :=
  eqb (gv mgB (sndT (var 1)) (pairT (fstT (var 1)) (var 0))) one * allB tS (sndT (var 1)) (pairT (fstT (var 1)) (var 0))

theorem kS_at (e B N : PTm k) :
    Γ ⊢[PRAAx] inst2 kS e (pairT B N) ≐ eqb (gv mgB N (pairT B e)) one * allB tS N (pairT B e) := by
  have h : inst2 kS e (pairT B N) =
      eqb (gv mgB (sndT (pairT B N)) (pairT (fstT (pairT B N)) e)) one *
        allB tS (sndT (pairT B N)) (pairT (fstT (pairT B N)) e) := by
    rw [show inst2 kS e (pairT B N) = Syn.subst ![e, pairT B N] kS from rfl]; simp
  rw [h]
  have eN : Γ ⊢[PRAAx] sndT (pairT B N) ≐ N := snd_pair _ _
  have eP : Γ ⊢[PRAAx] pairT (fstT (pairT B N)) e ≐ pairT B e := congrPairT (fst_pair _ _) (.eqRefl _)
  exact congrMul (congrEqb (congrAp2 _ eN eP) (.eqRefl _)) (congrAp2 _ eN eP)

theorem tS_at (i y : PTm k) :
    Γ ⊢[PRAAx] inst2 tS i y ≐ eqb (monus (inst2 sgB i y) (gv mgB i y)) zero := by
  have h : inst2 tS i y = eqb (monus (inst2 sgB i y) (gv mgB i y)) zero := by
    rw [show inst2 tS i y = Syn.subst ![i, y] tS from rfl]; simp
  rw [h]; exact .eqRefl _

/-- Every listed code `e < (2B + 1)^N` decodes to a vector with primitive magnitudes whose signs obey the
first-nonzero convention. -/
theorem signed_sound {B N r : PTm k} (hr : Γ ⊢[PRAAx] lt r (rank kS (pw (bse B) N) (pairT B N))) :
    Γ ⊢[PRAAx] lt (sel kS r (pw (bse B) N) (pairT B N)) (pw (bse B) N) ⋏
      ((gv mgB N (pairT B (sel kS r (pw (bse B) N) (pairT B N))) ≐ one) ⋏
        Fm.all (lt (var 0) (Syn.shift N) ⟶
          neg (inst2 tS (var 0) (Syn.shift (pairT B (sel kS r (pw (bse B) N) (pairT B N)))) ≐ zero))) := by
  have s := sel_spec kS hr
  have k := Prf.andE₁ (Prf.andE₂ s)
  have kk := kS_at (Γ := Γ) (sel kS r (pw (bse B) N) (pairT B N)) B N
  have f1 : Γ ⊢[PRAAx] neg (eqb (gv mgB N (pairT B (sel kS r (pw (bse B) N) (pairT B N)))) one ≐ zero) :=
    .impI (Prf.impE k.wk (kk.wk.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))))
  have f2 : Γ ⊢[PRAAx] allB tS N (pairT B (sel kS r (pw (bse B) N) (pairT B N))) ≐ one := by
    refine .orE (all_cases tS N _) ?_ Prf.hyp0
    exact .botE _ (Prf.impE k.wk (kk.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))
  exact .andI (Prf.andE₁ s) (.andI (eq_of_eqb_ne f1) (all_reflect tS f2))

/-- The list is duplicate-free. -/
theorem signed_inj {B N r r' : PTm k} (hr : Γ ⊢[PRAAx] lt r (rank kS (pw (bse B) N) (pairT B N)))
    (hr' : Γ ⊢[PRAAx] lt r' (rank kS (pw (bse B) N) (pairT B N)))
    (h : Γ ⊢[PRAAx] sel kS r (pw (bse B) N) (pairT B N) ≐ sel kS r' (pw (bse B) N) (pairT B N)) :
    Γ ⊢[PRAAx] r ≐ r' :=
  (Prf.andE₂ (Prf.andE₂ (sel_spec kS hr))).eqSymm.eqTrans
    ((congrAp2 _ h (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (sel_spec kS hr'))))

/-! ## Completeness -/

/-- The digit `s_i B + m_i` of a signed entry, over `0 = i`, `1 = ⟨B, x⟩`. -/
abbrev vS (S M : PTm 2) : PTm 2 := inst2 S (var 0) (sndT (var 1)) * fstT (var 1) + inst2 M (var 0) (sndT (var 1))

theorem vS_at (S M : PTm 2) (i B x : PTm k) :
    Γ ⊢[PRAAx] inst2 (vS S M) i (pairT B x) ≐ inst2 S i x * B + inst2 M i x := by
  have h : inst2 (vS S M) i (pairT B x) =
      inst2 S i (sndT (pairT B x)) * fstT (pairT B x) + inst2 M i (sndT (pairT B x)) := by
    rw [show inst2 (vS S M) i (pairT B x) = Syn.subst ![i, pairT B x] (vS S M) from rfl]; simp
  rw [h]
  exact congrAdd (congrMul (congrInst2 S (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
    (congrInst2 M (.eqRefl _) (snd_pair _ _))

theorem shP (a b : PTm k) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]
theorem shBse (B : PTm k) : Syn.shift (bse B) = bse (Syn.shift B) := by simp [Syn.shift]

theorem bse_pos (B : PTm k) : Γ ⊢[PRAAx] bse B ≐ succ (pred (bse B)) := congrSucc (pred_succ _).eqSymm

/-- Every normalized signed vector with magnitudes `≤ B` is the decoding of a listed code: its code `e`
has rank below the length, `sel (rank e) = e`, and the digits of `e` decode to the given signs and
magnitudes. -/
theorem signed_complete (S M : PTm 2) {B N x : PTm k}
    (bS : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 S (var 0) (Syn.shift x) ≐ zero) ⋎ (inst2 S (var 0) (Syn.shift x) ≐ one)))
    (zS : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 S (var 0) (Syn.shift x)) (inst2 M (var 0) (Syn.shift x))))
    (mB : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 M (var 0) (Syn.shift x)) (Syn.shift B)))
    (fS : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 S (var 0) (Syn.shift x)) (gv M (var 0) (Syn.shift x))))
    (hg : Γ ⊢[PRAAx] gv M N x ≐ one) :
    Γ ⊢[PRAAx] (lt (rank kS (code (vS S M) (bse B) (pairT B x) N) (pairT B N)) (rank kS (pw (bse B) N) (pairT B N)) ⋏
      (sel kS (rank kS (code (vS S M) (bse B) (pairT B x) N) (pairT B N)) (pw (bse B) N) (pairT B N) ≐
        code (vS S M) (bse B) (pairT B x) N)) ⋏
      Fm.all (lt (var 0) (Syn.shift N) ⟶
        (inst2 sgB (var 0) (pairT (Syn.shift B) (code (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x))
          (Syn.shift N))) ≐ inst2 S (var 0) (Syn.shift x)) ⋏
        (inst2 mgB (var 0) (pairT (Syn.shift B) (code (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x))
          (Syn.shift N))) ≐ inst2 M (var 0) (Syn.shift x))) := by
  -- the digits are below the base
  have hV : Γ ⊢[PRAAx] entriesLt (vS S M) (bse B) (pairT B x) N := by
    refine .allI (.impI ?_)
    rw [shP, shBse]
    exact lt_congr (vS_at S M _ _ _).eqSymm (.eqRefl _)
      (enc_lt (Prf.impE bS.allOpen.wk Prf.hyp0) (Prf.impE mB.allOpen.wk Prf.hyp0))
  have hVs : Γ.map Fm.shift ⊢[PRAAx] entriesLt (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x)) (Syn.shift N) := by
    have e := hV.shift
    simpa [Fm.shift, Syn.shift, entriesLt, Syn.subst_subst, Syn.up_succ, Syn.up_zero, Syn.shift_var] using e
  -- decoding, entry by entry
  have dec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 sgB (var 0) (pairT (Syn.shift B) (code (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x))
        (Syn.shift N))) ≐ inst2 S (var 0) (Syn.shift x)) ⋏
      (inst2 mgB (var 0) (pairT (Syn.shift B) (code (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x))
        (Syn.shift N))) ≐ inst2 M (var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    have cd := code_digit (bse_pos _) hVs.wk (Prf.hyp0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    have dv := cd.eqTrans (vS_at S M (var 0) (Syn.shift B) (Syn.shift x))
    have ed := enc_dec (Prf.impE bS.allOpen.wk Prf.hyp0) (Prf.impE zS.allOpen.wk Prf.hyp0) (Prf.impE mB.allOpen.wk Prf.hyp0)
    exact .andI ((sg_at _ _ _).eqTrans ((congrSgn (.eqRefl _) dv).eqTrans (Prf.andE₁ ed)))
      ((mg_at _ _ _).eqTrans ((congrMag (.eqRefl _) dv).eqTrans (Prf.andE₂ ed)))
  have eS : Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N)) =
      pairT (Syn.shift B) (code (vS S M) (bse (Syn.shift B)) (pairT (Syn.shift B) (Syn.shift x)) (Syn.shift N)) := by
    simp [Syn.shift]
  -- the magnitudes agree, so do their gcds and prefix gcds
  have mags : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 mgB (var 0) (Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N))) ≐ inst2 M (var 0) (Syn.shift x)) := by
    rw [eS]; exact .allI (.impI (Prf.andE₂ (Prf.impE dec.allOpen.wk Prf.hyp0)))
  have g1 := (gv_congr mgB M mags).eqTrans hg
  have pre := gv_congr_all mgB M mags
  -- the sign test passes at every index
  have tst : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      neg (inst2 tS (var 0) (Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N))) ≐ zero)) := by
    refine .allI (.impI ?_)
    have hi : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    have sgi : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 sgB (var 0) (Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N))) ≐ inst2 S (var 0) (Syn.shift x) := by
      rw [eS]; exact Prf.andE₁ (Prf.impE dec.allOpen.wk hi)
    have gi := Prf.impE pre.allOpen.wk (le_of_lt hi)
    have fi := Prf.impE fS.allOpen.wk hi
    have m0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        monus (inst2 sgB (var 0) (Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N))))
          (gv mgB (var 0) (Syn.shift (pairT B (code (vS S M) (bse B) (pairT B x) N)))) ≐ zero :=
      (congrMonus sgi gi).eqTrans fi
    have t1 := (tS_at (var 0) _).eqTrans (eqb_of_eq m0)
    exact .impI (succ_ne_zero' _ (t1.wk.eqSymm.eqTrans Prf.hyp0))
  have kept : Γ ⊢[PRAAx] neg (inst2 kS (code (vS S M) (bse B) (pairT B x) N) (pairT B N) ≐ zero) := by
    have v : Γ ⊢[PRAAx] inst2 kS (code (vS S M) (bse B) (pairT B x) N) (pairT B N) ≐ one :=
      (kS_at _ B N).eqTrans ((congrMul (eqb_of_eq g1) (all_intro tS tst)).eqTrans
        (by apply deriveNat; ipra_simps; ring))
    exact .impI (succ_ne_zero' _ (v.wk.eqSymm.eqTrans Prf.hyp0))
  have hlt := code_lt hV (le_refl N)
  exact .andI (.andI (rank_lt_size kS hlt kept) (sel_rank kS hlt kept)) dec

end LeanProofs.IPRA.DiophantineNumberTheory.SignedNorthcott
