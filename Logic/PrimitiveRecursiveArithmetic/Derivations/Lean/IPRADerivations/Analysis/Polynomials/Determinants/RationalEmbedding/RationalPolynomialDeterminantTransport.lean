import IPRADerivations.Analysis.Polynomials.CompanionMatrices.RationalPolynomialMonicCompanionGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Determinants.RationalEmbedding.RationalPolynomialDeterminantGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialDegreeGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantCongruence

/-!
# Transport a numerical rational determinant through its embedded cells

The target matrix may use different outer list codes. Agreement of the
original bounded coefficient values suffices to transport the determinant,
its Horner evaluation, and the result of the actual rational degree scan.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantTransport

open_ipra
open RationalGaussianEmbedding (embed)
open RationalPolynomialMonicCompanionGaussianEmbedding (rowsEmbedded row_embedded_at)
open RationalPolynomialDeterminantTermsGaussianEmbedding
  (embeddedTable table_cell entriesEqual embedded_entries_to_codes)
open GaussianPolynomialDeterminantCongruence (matrixEntries rowEntries)
open GaussianPolynomialDeterminantTerms (cell)
open RationalPolynomialDeterminantGaussianEmbedding (determinant determinant_length coefficient_embedding)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def matrixEmbedded (M P m L : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  rowsEmbedded (entry (Syn.shift M) (var 0)) (entry (Syn.shift P) (var 0)) (Syn.shift m) (Syn.shift L))

ipra_subst matrixEmbedded [Syn.subst_shift, Syn.shift_subst]

theorem cell_embedded (M P m L r j : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] embeddedEntries (cell M r j) (cell P r j) (succ L) := by
  have row : Γ ⊢[PRAAx] lt r m ⟶ rowsEmbedded (entry M r) (entry P r) m L := by
    simpa [matrixEmbedded] using h.allE r
  exact row_embedded_at _ _ _ _ _ (.impE row hr) hj

theorem cell_agreement (M P m L r j : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] entriesEqual (cell (embeddedTable M m L) r j) (cell P r j) (succ L) := by
  let C := cell (embeddedTable M m L) r j
  let D := RationalPolynomialGaussianEmbedding.coefficients (cell M r j) (succ L)
  have dd := embedded_entries_to_codes _ _ _ (cell_embedded M P m L r j h hr hj)
  let phi : Fm PTm 3 := entriesEqual (var 0) (var 1) (var 2)
  let Q := cell P r j
  have hd : Γ ⊢[PRAAx] phi.subst ![D,Q,succ L] := by simpa [phi,D,Q] using dd
  have moved := Prf.eqSubst phi ![D,Q,succ L] ![C,Q,succ L]
    (fun i => by fin_cases i; exact (table_cell M m L r j hr hj).eqSymm; exact .eqRefl _; exact .eqRefl _) hd
  simpa [phi,C,Q] using moved

theorem row_agreement (M P m L r : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] rowEntries (embeddedTable M m L) P m L r := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] matrixEmbedded (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hr' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hr.shift
  simpa [Syn.shift] using cell_agreement (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L)
    (Syn.shift r) (var 0) h'.wk hr'.wk Prf.hyp0

theorem matrix_agreement (M P m L : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L) :
    Γ ⊢[PRAAx] matrixEntries (embeddedTable M m L) P m L := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] matrixEmbedded (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [Syn.shift] using row_agreement (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (var 0) h'.wk Prf.hyp0

theorem coefficient_transport (M P m L s : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L)
    (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    embed (entry (determinant M m L) s) ≐ entry (GaussianPolynomialDeterminant.determinant P m L) s :=
  (coefficient_embedding M m L s hs).eqTrans (GaussianPolynomialDeterminantCongruence.determinant_coefficient
    (embeddedTable M m L) P m L s (matrix_agreement M P m L h) hs)

theorem determinant_transport (M P m L : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L) :
    Γ ⊢[PRAAx] embeddedEntries (determinant M m L) (GaussianPolynomialDeterminant.determinant P m L) (succ (m*L)) := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] matrixEmbedded (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hs : lt (var 0) (succ (Syn.shift m*Syn.shift L)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (Syn.shift m*Syn.shift L) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa [Syn.shift] using coefficient_transport (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (var 0) h'.wk hs

theorem evaluation_transport (M P m L x : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L) :
    Γ ⊢[PRAAx] embed (RationalPolynomialGaussianEmbedding.evaluate (determinant M m L) x) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialDeterminant.determinant P m L) (embed x) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ _
    (determinant_length M m L) (GaussianPolynomialDeterminant.determinant_length P m L)
    (determinant_transport M P m L h)

theorem flag_transport (M P m L : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L) :
    Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.flag (determinant M m L) (m*L) ≐
      GaussianRationalPolynomialDegree.flag (GaussianPolynomialDeterminant.determinant P m L) (m*L) :=
  RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy _ _ _ (determinant_transport M P m L h)

theorem degree_transport (M P m L : PTm n) (h : Γ ⊢[PRAAx] matrixEmbedded M P m L) :
    Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.degree (determinant M m L) (m*L) ≐
      GaussianRationalPolynomialDegree.degree (GaussianPolynomialDeterminant.determinant P m L) (m*L) :=
  RationalPolynomialDegreeGaussianEmbedding.degree_conjugacy _ _ _ (determinant_transport M P m L h)

theorem actual_rational_determinant_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (matrixEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      embeddedEntries (determinant (var 0) (var 2) (var 3))
        (GaussianPolynomialDeterminant.determinant (var 1) (var 2) (var 3)) (succ (var 2*var 3))) :=
  closeUniv 4 (.impI (determinant_transport _ _ _ _ Prf.hyp0))

theorem actual_rational_determinant_degree_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (matrixEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      (RationalPolynomialDegreeGaussianEmbedding.flag (determinant (var 0) (var 2) (var 3)) (var 2*var 3) ≐
        GaussianRationalPolynomialDegree.flag (GaussianPolynomialDeterminant.determinant (var 1) (var 2) (var 3)) (var 2*var 3) ⋏
        RationalPolynomialDegreeGaussianEmbedding.degree (determinant (var 0) (var 2) (var 3)) (var 2*var 3) ≐
          GaussianRationalPolynomialDegree.degree (GaussianPolynomialDeterminant.determinant (var 1) (var 2) (var 3)) (var 2*var 3))) :=
  closeUniv 4 (.impI (.andI (flag_transport _ _ _ _ Prf.hyp0) (degree_transport _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantTransport
