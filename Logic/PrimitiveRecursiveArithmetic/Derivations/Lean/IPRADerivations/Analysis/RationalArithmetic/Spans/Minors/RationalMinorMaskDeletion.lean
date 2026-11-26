import IPRADerivations.Analysis.RationalArithmetic.Spans.Minors.RationalMinorMaskExtension

/-!
# Deleting a selected column from an actual minor mask

Complement the in-range digits, insert a one in the complementary mask,
then complement again. This keeps the binary code bounded by the same
dimension and removes exactly the requested entry and its filtered count.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorMaskDeletion

open_ipra
open RationalSelectedMinors (count)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalMinorFreeColumn (complementBody complement_at missingCount complementary_count bit_cases)
open RationalMinorMaskExtension (insert new_bit old_bit insert_count)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB inst2_sgB)
open LeanProofs.IPRA.Foundations.MixedRadix (Cd dP)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def flip (N M : PTm n) : PTm n := Cd (two : PTm 2) complementBody N M
def erase (N M c : PTm n) : PTm n := flip N (insert N (flip N M) c)

ipra_subst flip

ipra_subst erase

theorem complement_digit_bounds (N M : PTm n) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ lt (inst2 complementBody (var 0) (Syn.shift M))
      (inst2 (two : PTm 2) (var 0) (Syn.shift M))) := by
  refine .allI (.impI ?_)
  rw [complement_at]
  have upper : inst2 (two : PTm 2) (var 0) (Syn.shift M) = two := by simp [inst2,two,one]
  rw [upper]
  refine .orE (bit_cases (var 0) (Syn.shift M)) ?_ ?_
  · exact lt_congr ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one)).eqSymm (.eqRefl _) (le_refl two)
  · exact lt_congr ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one)).eqSymm (.eqRefl _) (le_succ_self one)

theorem flip_bound (N M : PTm n) : Γ ⊢[PRAAx] lt (flip N M) (pw two N) :=
  lt_congr (.eqRefl _) (RationalFiniteSpanCover.places N M)
    (Foundations.MixedRadix.code_lt _ _ _ _ (complement_digit_bounds N M))

theorem flip_bit (N M i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bit (flip N M) i ≐ monus one (bit M i) := by
  let t := monus N (succ i)
  have span : Γ ⊢[PRAAx] succ i+t ≐ N := (eq_add_of_le hi).eqSymm
  have decoded := Foundations.MixedRadix.decode (complement_digit_bounds (Γ := Γ) (succ i+t) M)
  have twoAt : inst2 (two : PTm 2) i M = (two : PTm n) := by simp [inst2,two,one]
  rw [twoAt,complement_at] at decoded
  have codeEq : Γ ⊢[PRAAx] Cd (two : PTm 2) complementBody (succ i+t) M ≐ flip N M :=
    congrAp2 (sumF (dP (two : PTm 2) complementBody)) span (.eqRefl _)
  exact (congrAp2 remF (congrAp2 quoF codeEq (RationalFiniteSpanCover.places i M)) (.eqRefl two)).eqSymm.eqTrans decoded

theorem count_flipped (N M : PTm n) : Γ ⊢[PRAAx] count N (flip N M) ≐ missingCount N M := by
  refine sum_congr_bounded (sgB bitBody) (sgB complementBody) (flip N M) M N (.allI (.impI ?_))
  let N' := Syn.shift N
  let M' := Syn.shift M
  let Δ := lt (var 0) N' :: Γ.map Fm.shift
  have e := flip_bit N' M' (var 0) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) N')
  rw [inst2_sgB,inst2_sgB,bit_body_at,complement_at]
  simpa only [Δ,N',M',Syn.shift,subst_flip,Signum.sg] using
    congrMonus (.eqRefl one) (congrMonus (.eqRefl one) e)

theorem count_complements (N M : PTm n) : Γ ⊢[PRAAx] count N M + count N (flip N M) ≐ N :=
  (congrAdd (.eqRefl _) (count_flipped N M)).eqTrans (complementary_count N M)

theorem erase_bound (N M c : PTm n) : Γ ⊢[PRAAx] lt (erase N M c) (pw two N) := flip_bound N _

theorem erased_bit (N M c : PTm n) (hc : Γ ⊢[PRAAx] lt c N) : Γ ⊢[PRAAx] bit (erase N M c) c ≐ zero :=
  (flip_bit N (insert N (flip N M) c) c hc).eqTrans
    ((congrMonus (.eqRefl one) (new_bit N (flip N M) c hc)).eqTrans (monus_self one))

theorem other_bit (N M c i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) (hne : Γ ⊢[PRAAx] neg (i ≐ c)) :
    Γ ⊢[PRAAx] bit (erase N M c) i ≐ bit M i := by
  have triple := (flip_bit N (insert N (flip N M) c) i hi).eqTrans
    (congrMonus (.eqRefl one) ((old_bit N (flip N M) c i hi hne).eqTrans (flip_bit N M i hi)))
  refine triple.eqTrans (.orE (bit_cases i M) ?_ ?_)
  · exact ((congrMonus (.eqRefl one) ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one))).eqTrans
      (monus_self one)).eqTrans Prf.hyp0.eqSymm
  · exact ((congrMonus (.eqRefl one) ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one))).eqTrans
      (monus_zero one)).eqTrans Prf.hyp0.eqSymm

theorem erase_count (N M c : PTm n) (hc : Γ ⊢[PRAAx] lt c N) (hb : Γ ⊢[PRAAx] bit M c ≐ one) :
    Γ ⊢[PRAAx] succ (count N (erase N M c)) ≐ count N M := by
  let B := count N (flip N M)
  let E := count N (erase N M c)
  have z := (flip_bit N M c hc).eqTrans ((congrMonus (.eqRefl one) hb).eqTrans (monus_self one))
  have insertion := insert_count N (flip N M) c hc z
  have newTotal : Γ ⊢[PRAAx] succ B + E ≐ N :=
    (congrAdd insertion.eqSymm (.eqRefl E)).eqTrans (count_complements N (insert N (flip N M) c))
  have shiftOne : Γ ⊢[PRAAx] B + succ E ≐ succ B + E := by ipra_ring
  exact add_left_cancel (shiftOne.eqTrans (newTotal.eqTrans ((add_comm B (count N M)).eqTrans (count_complements N M)).eqSymm))

theorem actual_erased_mask_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (erase (var 0) (var 1) (var 2)) (pw two (var 0))) := closeUniv 3 (erase_bound _ _ _)

theorem actual_erased_mask_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ bit (erase (var 0) (var 1) (var 2)) (var 2) ≐ zero) :=
  closeUniv 3 (.impI (erased_bit _ _ _ Prf.hyp0))

theorem actual_erased_mask_other_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ neg (var 3 ≐ var 2) ⟶ bit (erase (var 0) (var 1) (var 2)) (var 3) ≐ bit (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (other_bit _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_erased_mask_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ bit (var 1) (var 2) ≐ one ⟶ succ (count (var 0) (erase (var 0) (var 1) (var 2))) ≐ count (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (erase_count _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalMinorMaskDeletion
