import IPRADerivations.Analysis.RationalSumReversal
import IPRADerivations.Analysis.RationalSumAdditivity

/-!
# Mirror pairing on an even rational mesh

For internal midpoint N, the literal sum through index 2N equals
the sum of rows paired at i and 2N-i for i<N, plus the midpoint row.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSumMirror

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalFiniteSumReversal (data reverseBody reverse_body_at)
open RationalArithmetic (add)
open RationalAlgebra (add_congr add_associative)
open RationalFiniteSum (sum term)
open RationalSumAdditivity (addedBody sum_additive added_term)
open RationalSumSegments (sum_congr split)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mirrorBody (f : PTm 2) : PTm 2 := addedBody f (reverseBody (offB f))

private def suffixData (N x : PTm n) : PTm n := data (succ N) (pairT N x)

def mirrorData (N x : PTm n) : PTm n := pairT x (suffixData N x)

@[simp] theorem subst_mirrorData {l : ℕ} (σ : Fin n → PTm l) (N x : PTm n) :
    Syn.subst σ (mirrorData N x) = mirrorData (Syn.subst σ N) (Syn.subst σ x) := by
  simp [mirrorData,suffixData]

private theorem reverse_index (i N : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] N+monus N i ≐ monus (N+N) i := by
  have rewrite : Γ ⊢[PRAAx] N+N ≐ (N+monus N i)+i :=
    (congrAdd (.eqRefl _) (eq_add_of_le hi)).eqTrans (by ipra_ring)
  have balance : Γ ⊢[PRAAx] monus (N+N) i ≐ monus ((N+monus N i)+i) (zero+i) :=
    congrMonus rewrite (zero_add i).eqSymm
  exact (balance.eqTrans ((monus_add_add _ _ _).eqTrans (monus_zero _))).eqSymm

private theorem suffix_at (f : PTm 2) (i N x : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] term (reverseBody (offB f)) i (suffixData N x) ≐
      term f (monus (N+N) i) x := by
  have h := reverse_body_at (Γ := Γ) (offB f) i (succ N) (pairT N x)
  exact h.eqTrans ((congrInst2 (offB f) (succ_monus_succ N i) (.eqRefl _)).eqTrans
    ((offset_at f N (monus N i) x).eqTrans (congrInst2 f (reverse_index i N hi) (.eqRefl _))))

theorem mirror_at (f : PTm 2) (i N x : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] term (mirrorBody f) i (mirrorData N x) ≐
      add (term f i x) (term f (monus (N+N) i) x) :=
  (added_term f (reverseBody (offB f)) i x (suffixData N x)).eqTrans
    (add_congr (.eqRefl _) (suffix_at f i N x hi))

theorem mirror_sum (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] add (sum f (N+N) x) (term f (N+N) x) ≐
      add (sum (mirrorBody f) N (mirrorData N x)) (term f N x) := by
  let g := reverseBody (offB f)
  let y := suffixData N x
  have last : Γ ⊢[PRAAx] term g N y ≐ term f N x := by
    have middle : Γ ⊢[PRAAx] monus (N+N) N ≐ N :=
      (congrMonus (.eqRefl _) (zero_add N).eqSymm).eqTrans
        ((monus_add_add N zero N).eqTrans (monus_zero N))
    exact (suffix_at f N N x (le_refl N)).eqTrans (congrInst2 f middle (.eqRefl _))
  have parts := (RationalFiniteSum.sum_succ (Γ := Γ) f (N+N) x).eqSymm.eqTrans
    ((sum_congr f (add_succ N N).eqSymm (.eqRefl x)).eqTrans (split f N (succ N) x))
  have reverseSuffix := RationalSumReversal.reverse (Γ := Γ) (offB f) (succ N) (pairT N x)
  have suffix : Γ ⊢[PRAAx] sum (offB f) (succ N) (pairT N x) ≐ add (sum g N y) (term f N x) :=
    reverseSuffix.eqSymm.eqTrans ((RationalFiniteSum.sum_succ g N y).eqTrans
      (add_congr (.eqRefl _) last))
  exact parts.eqTrans ((add_congr (.eqRefl _) suffix).eqTrans
    ((add_associative _ _ _).eqSymm.eqTrans (add_congr (sum_additive f g N x y).eqSymm (.eqRefl _))))

theorem actual_scalar_rational_mirror_pairing_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (add (sum f (var 0+var 0) (var 1)) (term f (var 0+var 0) (var 1)) ≐
        add (sum (mirrorBody f) (var 0) (mirrorData (var 0) (var 1))) (term f (var 0) (var 1))) :=
  closeUniv 2 (mirror_sum f _ _)

end LeanProofs.IPRA.Analysis.RationalSumMirror
