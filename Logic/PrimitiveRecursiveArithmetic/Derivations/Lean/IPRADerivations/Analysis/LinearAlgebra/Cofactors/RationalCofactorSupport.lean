import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalCofactorVector
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminantLaplace

/-!
# Ordered support and the common cofactor sign of the actual vector

Read each supported source column from the actual augmented mask. Its
filtered position is the determinant's column index, which identifies the
stored parity test. The difference between the two sign conventions is
one common unit for the entire row dot product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorSupport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open RationalSelectedMinors (count index index_bound index_selected)
open RationalSubtupleSpan (bit)
open RationalMinorFreeColumn (free bit_cases)
open RationalMinorAugmentation (extendedColumn free_prefix_count)
open RationalMinorMaskExtension (index_rank prefix_count_before)
open RationalMaximalMinors (rank bestColumn)
open RationalCofactorVector (positionParity)
open GaussianScalarDeterminantLaplace (unitSign sign_bit_congr unit_sign_add)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def supportedColumn (P d r : PTm n) : PTm n := index d (extendedColumn P d) r

@[simp] theorem subst_supportedColumn {k : ℕ} (σ : Fin n → PTm k) (P d r : PTm n) :
    Syn.subst σ (supportedColumn P d r) = supportedColumn (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ r) := by
  simp [supportedColumn]

theorem supported_label (P d r : PTm n) (h : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d))) : Γ ⊢[PRAAx]
    lt (supportedColumn P d r) d ⋏ (bit (extendedColumn P d) (supportedColumn P d r) ≐ one ⋏
      count (supportedColumn P d r) (extendedColumn P d) ≐ r) := by
  let M := extendedColumn P d
  let j := supportedColumn P d r
  have oneBit : Γ ⊢[PRAAx] bit M j ≐ one :=
    .orE (bit_cases j M) (.botE _ (.impE (index_selected d M r h).wk Prf.hyp0)) Prf.hyp0
  exact .andI (index_bound d M r h) (.andI oneBit (index_rank d M r h))

theorem remainder_parity (a : PTm n) : Γ ⊢[PRAAx] rem a two ≐ par a := by
  have h : Γ ⊢[PRAAx] lt (par a) two := .orE (par_cases a)
    (lt_congr Prf.hyp0.eqSymm (.eqRefl _) (le_succ_self one))
    (lt_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl two))
  exact (Foundations.RuntimeWordAppend.divide_unique two a (half a) (par a) (le_succ_self one) (half_par a) h).andE₂

theorem support_position_parity (P d r : PTm n) (h : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d))) : Γ ⊢[PRAAx]
    positionParity P d (supportedColumn P d r) ≐ par (free P d+r) :=
  (congrAp2 remF (congrAdd (.eqRefl _) (supported_label P d r h).andE₂.andE₂) (.eqRefl two)).eqTrans
    (remainder_parity (free P d+r))

theorem free_position_parity (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) : Γ ⊢[PRAAx] positionParity P d (free P d) ≐ zero := by
  let c := free P d
  have countBefore := prefix_count_before d (bestColumn P d) c c (le_of_lt (RationalMinorFreeColumn.free_column_spec P d h).andE₁) (le_refl c)
  have e : Γ ⊢[PRAAx] count c (extendedColumn P d) ≐ c := countBefore.eqTrans (free_prefix_count P d h)
  exact (congrAp2 remF (congrAdd (.eqRefl _) e) (.eqRefl two)).eqTrans
    ((remainder_parity (c+c)).eqTrans (par_self_add c))

theorem common_unit (m c r : PTm n) : Γ ⊢[PRAAx] unitSign (m+r) ≐
    qmul (unitSign (m+c)) (unitSign (c+r)) := by
  have e : Γ ⊢[PRAAx] (m+c)+(c+r) ≐ (m+r)+two*c := by ipra_ring
  have p := (congrAp1 parF e).eqTrans (par_add_two (m+r) c)
  exact (sign_bit_congr p).eqSymm.eqTrans (unit_sign_add (m+c) (c+r))

theorem actual_cofactor_support_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (count (var 1) (extendedColumn (var 0) (var 1))) ⟶
      lt (supportedColumn (var 0) (var 1) (var 2)) (var 1) ⋏
        (bit (extendedColumn (var 0) (var 1)) (supportedColumn (var 0) (var 1) (var 2)) ≐ one ⋏
          count (supportedColumn (var 0) (var 1) (var 2)) (extendedColumn (var 0) (var 1)) ≐ var 2)) :=
  closeUniv 3 (.impI (supported_label _ _ _ Prf.hyp0))

theorem actual_cofactor_support_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (count (var 1) (extendedColumn (var 0) (var 1))) ⟶
      positionParity (var 0) (var 1) (supportedColumn (var 0) (var 1) (var 2)) ≐ par (free (var 0) (var 1)+var 2)) :=
  closeUniv 3 (.impI (support_position_parity _ _ _ Prf.hyp0))

theorem actual_cofactor_common_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (unitSign (var 0+var 2) ≐ qmul (unitSign (var 0+var 1)) (unitSign (var 1+var 2))) := closeUniv 3 (common_unit _ _ _)

end LeanProofs.IPRA.Analysis.RationalCofactorSupport
