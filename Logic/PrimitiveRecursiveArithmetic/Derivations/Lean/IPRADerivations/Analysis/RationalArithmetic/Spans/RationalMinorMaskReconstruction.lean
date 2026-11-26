import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalMinorMaskDeletion
import IPRADerivations.Core.CongruenceTactic

/-!
# Exact reconstruction of a bounded minor mask after deletion

Decode and re-encode in the original fixed binary radix. Two bounded
masks with the same in-range digits are the same numerical word. Inserting
a formerly selected digit into its erased mask therefore recovers the
original word, including its filtered order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorMaskReconstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open RationalSubtupleSpan (bit)
open RationalMinorMaskExtension (insert insert_bound new_bit old_bit)
open RationalMinorMaskDeletion (erase erased_bit other_bit)
open RationalFiniteSpanCover (places)
open LeanProofs.IPRA.Foundations.MixedRadix (Cd dP Pl inst2_dP)
open LeanProofs.IPRA.Foundations.MixedRadixExpansion (dgB inst2_dgB reencode)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decoded (N M : PTm n) : PTm n := Cd (two : PTm 2) (dgB (two : PTm 2)) N (pairT M zero)
def bitAgreement (N M K : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ bit (Syn.shift M) (var 0) ≐ bit (Syn.shift K) (var 0))

@[simp] theorem subst_bitAgreement {l : ℕ} (σ : Fin n → PTm l) (N M K : PTm n) :
    (bitAgreement N M K).subst σ = bitAgreement (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ K) := by
  simp [bitAgreement,Syn.subst_shift,Syn.shift_subst]

theorem decoded_bit (M i : PTm n) : Γ ⊢[PRAAx] inst2 (dgB (two : PTm 2)) i (pairT M zero) ≐ bit M i := by
  rw [inst2_dgB]
  have atTwo : inst2 (two : PTm 2) i (pairT M zero) = (two : PTm n) := by simp [inst2,two,one]
  rw [atTwo]
  exact congrAp2 remF (congrAp2 quoF (fst_pair M zero) (places i (pairT M zero))) (.eqRefl two)

theorem decoded_word (N M : PTm n) (h : Γ ⊢[PRAAx] lt M (pw two N)) : Γ ⊢[PRAAx] decoded N M ≐ M := by
  let y := pairT M zero
  have positive : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶ lt zero (inst2 (two : PTm 2) (var 0) (Syn.shift y))) := by
    refine .allI (.impI ?_)
    have proof : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] lt zero two := le_succ_self one
    simpa [inst2,two,one] using proof
  have below : Γ ⊢[PRAAx] lt (fstT y) (Pl (two : PTm 2) N y) :=
    lt_congr (fst_pair M zero).eqSymm (places N y).eqSymm h
  exact (reencode positive below).eqTrans (fst_pair M zero)

theorem agreement_at (N M K i : PTm n) (h : Γ ⊢[PRAAx] bitAgreement N M K) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bit M i ≐ bit K i := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ bit M i ≐ bit K i := by simpa [bitAgreement] using h.allE i
  exact .impE rule hi

theorem binary_extensional (N M K : PTm n) (hm : Γ ⊢[PRAAx] lt M (pw two N)) (hk : Γ ⊢[PRAAx] lt K (pw two N))
    (h : Γ ⊢[PRAAx] bitAgreement N M K) : Γ ⊢[PRAAx] M ≐ K := by
  have rebuilt : Γ ⊢[PRAAx] decoded N M ≐ decoded N K := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let a := Syn.shift N
    let b := Syn.shift M
    let c := Syn.shift K
    let Δ := lt (var 0) a :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] bitAgreement a b c := by
      simpa only [Δ,a,b,c,Fm.shift,Syn.shift,subst_bitAgreement] using h.shift.wk
    have hi : Δ ⊢[PRAAx] lt (var 0) a := Prf.hyp0
    simp only [Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero,inst2_dP]
    exact congrMul ((decoded_bit b (var 0)).eqTrans ((agreement_at a b c (var 0) hs hi).eqTrans (decoded_bit c (var 0)).eqSymm))
      ((places (var 0) (pairT b zero)).eqTrans (places (var 0) (pairT c zero)).eqSymm)
  exact (decoded_word N M hm).eqSymm.eqTrans (rebuilt.eqTrans (decoded_word N K hk))

theorem bit_congr {M K i j : PTm n} (h : Γ ⊢[PRAAx] M ≐ K) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] bit M i ≐ bit K j := by
  ipra_congr (bit (var 0) (var 1) : PTm 2) with [h, hi]

theorem restored_bit (N M c i : PTm n) (hc : Γ ⊢[PRAAx] lt c N) (hi : Γ ⊢[PRAAx] lt i N)
    (hs : Γ ⊢[PRAAx] bit M c ≐ one) : Γ ⊢[PRAAx] bit (insert N (erase N M c) c) i ≐ bit M i := by
  refine .orE (eq_or_ne i c) ?_ ?_
  · exact (bit_congr (.eqRefl _) Prf.hyp0).eqTrans
      ((new_bit N (erase N M c) c hc.wk).eqTrans (hs.wk.eqSymm.eqTrans (bit_congr (.eqRefl M) Prf.hyp0.eqSymm)))
  · exact (old_bit N (erase N M c) c i hi.wk Prf.hyp0).eqTrans (other_bit N M c i hi.wk Prf.hyp0)

theorem restore_erased (N M c : PTm n) (hm : Γ ⊢[PRAAx] lt M (pw two N)) (hc : Γ ⊢[PRAAx] lt c N)
    (hs : Γ ⊢[PRAAx] bit M c ≐ one) : Γ ⊢[PRAAx] insert N (erase N M c) c ≐ M := by
  apply binary_extensional N _ M (insert_bound N _ _) hm
  refine .allI (.impI ?_)
  let a := Syn.shift N
  let b := Syn.shift M
  let j := Syn.shift c
  let Δ := lt (var 0) a :: Γ.map Fm.shift
  have hq : Δ ⊢[PRAAx] lt j a := by simpa only [Δ,a,j,Fm.shift,subst_lt,Syn.shift] using hc.shift.wk
  have good : Δ ⊢[PRAAx] bit b j ≐ one := by
    simpa only [Δ,b,j,Fm.shift,Fm.subst_eq,RationalSubtupleSpan.subst_bit,Syn.shift,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hs.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) a := Prf.hyp0
  simpa only [Δ,a,b,j,Syn.shift,RationalMinorMaskExtension.subst_insert,RationalMinorMaskDeletion.subst_erase] using
    restored_bit a b j (var 0) hq hi good

theorem actual_binary_mask_extensional_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (pw two (var 0)) ⟶ lt (var 2) (pw two (var 0)) ⟶ bitAgreement (var 0) (var 1) (var 2) ⟶ var 1 ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (binary_extensional _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_binary_mask_delete_insert_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (pw two (var 0)) ⟶ lt (var 2) (var 0) ⟶ bit (var 1) (var 2) ≐ one ⟶
      insert (var 0) (erase (var 0) (var 1) (var 2)) (var 2) ≐ var 1) :=
  closeUniv 3 (.impI (.impI (.impI (restore_erased _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalMinorMaskReconstruction
