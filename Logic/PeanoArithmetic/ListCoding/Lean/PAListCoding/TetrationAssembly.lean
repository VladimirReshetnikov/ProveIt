import PAListCoding.IterationDioph
import PAListCoding.TetrationDiophantine
import PAListCoding.CipherOnes
import PAListCoding.CipherRelations

/-!
# Final Lean assembly for tetration

The mathematical work is modular: one encoded tower step is Diophantine,
exact variable-length iteration follows from bounded universals, and the
state code is injective.  This file first combines those ingredients under
five arithmetic-cipher closure contracts, then discharges the contracts
through `CipherOnes` and `CipherRelations` and exposes the unconditional
public result-first tetration graph.
-/

namespace PAListCoding

namespace TetrationAssembly

open BoundedCipher BoundedCipherDioph CipherCircuit CircuitDioph
open IterationDioph SparseCipher
open Fin2
open scoped Dioph

/-- The result-first tetration graph is Diophantine once the arithmetic
cipher primitives satisfy their substitution contracts. -/
theorem naturalTetrationGraph_diophantine_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    Dioph NaturalTetrationGraph := by
  have dresult : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &0) := D&0
  have dbase : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &1) := D&1
  have dheight : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &2) := D&2
  have done : Dioph.DiophFn
      (fun _v : Vector3 ℕ 3 => 1) := BoundedDioph.constFn_dioph 1
  have dstart : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => tetrationStateCode (v &1) 1) :=
    tetrationStateCode_diophFn dbase done
  have dfinish : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => tetrationStateCode (v &1) (v &0)) :=
    tetrationStateCode_diophFn dbase dresult
  have hiter : Dioph {v : Vector3 ℕ 3 |
      ExactIter TetrationStep (v &2)
        (tetrationStateCode (v &1) 1)
        (tetrationStateCode (v &1) (v &0))} :=
    exactIter_dioph hcode hconstFixed hconst hindex hmul
      tetrationStep_diophantine dheight dstart dfinish
  apply Dioph.ext hiter
  intro v
  change
    ExactIter TetrationStep (v &2)
        (tetrationStateCode (v &1) 1)
        (tetrationStateCode (v &1) (v &0)) ↔
      v &0 = tetration (v &1) (v &2)
  exact (tetration_eq_iff_exactIter (v &0) (v &1) (v &2)).symm

/-- Function-graph form of the same result. -/
theorem naturalTetration_diophantineFunction_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    Dioph.DiophFn NaturalTetrationFunction := by
  apply (Dioph.diophFn_vec NaturalTetrationFunction).2
  apply Dioph.ext
    (naturalTetrationGraph_diophantine_of_cipherClosures
      hcode hconstFixed hconst hindex hmul)
  intro v
  change
    (v &0 = tetration (v &1) (v &2)) ↔
      (tetration (v &1) (v &2) = v &0)
  exact eq_comm

/-- Unfolded witness contract: a single integer polynomial, with a fixed
existential tuple of natural variables, defines the tetration graph. -/
theorem naturalTetration_polynomial_exists_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    ∃ (β : Type) (p : Poly (Fin2 3 ⊕ β)),
      ∀ v : Vector3 ℕ 3,
        v &0 = tetration (v &1) (v &2) ↔
          ∃ t : β → ℕ, p (Sum.elim v t) = 0 :=
  naturalTetrationGraph_diophantine_of_cipherClosures
    hcode hconstFixed hconst hindex hmul

end TetrationAssembly

open Fin2
open scoped Dioph

/-! ## Discharging the primitive closure contracts

The sparse one-columns are the only non-elementary arithmetic ingredient in
the cipher compiler.  `CipherOnes.onesCodes_dioph` constructs them from one
finite arithmetic certificate; `CipherRelations` then derives all five
primitive closures used by the bounded iteration theorem.  Keeping these
bridges here makes the public theorem unconditional while preserving the
modular conditional assembly above.
-/

private theorem tetrationOnesSubstitutionClosed :
    CipherRelations.OnesSubstitutionClosed := by
  intro alpha len q ones shifted dlen dq dones dshifted
  exact CipherOnes.onesCodes_dioph dlen dq dones dshifted

private theorem tetrationCodeSubstitutionClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.Code :=
  CipherRelations.code_closed_of_ones tetrationOnesSubstitutionClosed

private theorem tetrationFixedConstSubstitutionClosed :
    ∀ k, CircuitDioph.TernarySubstitutionClosed
      (fun len q code ↦ SparseCipher.ConstCode len q k code) :=
  CipherRelations.constCode_fixed_closed_of_ones
    tetrationOnesSubstitutionClosed

/-- The parameter-valued constant column uses the same four-function
substitution contract as the bounded-cipher compiler. -/
private theorem tetrationConstSubstitutionClosed :
    BoundedCipherDioph.QuaternarySubstitutionClosed
      SparseCipher.ConstCode := by
  -- The relation layer deliberately defines this contract without importing
  -- the downstream bounded compiler; unfolding by `change` identifies the
  -- two definitionally equal interfaces without fragile metavariable search.
  change CipherRelations.QuaternarySubstitutionClosed SparseCipher.ConstCode
  exact CipherRelations.constCode_closed_of_ones
    tetrationOnesSubstitutionClosed

private theorem tetrationIndexSubstitutionClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.IndexCode :=
  CipherRelations.indexCode_closed_of_ones tetrationOnesSubstitutionClosed

private theorem tetrationMulSubstitutionClosed :
    CircuitDioph.QuinarySubstitutionClosed BoundedCipher.MulRel :=
  CipherRelations.mulRel_closed_of_ones tetrationOnesSubstitutionClosed

/-- The result-first graph `(result, base, height)` of natural tetration is
Diophantine.  Our convention is `tetration base 0 = 1` and
`tetration base (height + 1) = base ^ tetration base height`. -/
theorem naturalTetrationGraph_diophantine : Dioph NaturalTetrationGraph :=
  TetrationAssembly.naturalTetrationGraph_diophantine_of_cipherClosures
    tetrationCodeSubstitutionClosed
    tetrationFixedConstSubstitutionClosed
    tetrationConstSubstitutionClosed
    tetrationIndexSubstitutionClosed
    tetrationMulSubstitutionClosed

/-- Natural tetration is a Diophantine function of `(base, height)`. -/
theorem naturalTetration_diophantineFunction :
    Dioph.DiophFn NaturalTetrationFunction :=
  TetrationAssembly.naturalTetration_diophantineFunction_of_cipherClosures
    tetrationCodeSubstitutionClosed
    tetrationFixedConstSubstitutionClosed
    tetrationConstSubstitutionClosed
    tetrationIndexSubstitutionClosed
    tetrationMulSubstitutionClosed

/-- Unfolded polynomial witness for the result-first tetration graph. -/
theorem naturalTetration_polynomial_exists :
    ∃ (β : Type) (p : Poly (Fin2 3 ⊕ β)),
      ∀ v : Vector3 ℕ 3,
        v &0 = tetration (v &1) (v &2) ↔
          ∃ t : β → ℕ, p (Sum.elim v t) = 0 :=
  TetrationAssembly.naturalTetration_polynomial_exists_of_cipherClosures
    tetrationCodeSubstitutionClosed
    tetrationFixedConstSubstitutionClosed
    tetrationConstSubstitutionClosed
    tetrationIndexSubstitutionClosed
    tetrationMulSubstitutionClosed

end PAListCoding
