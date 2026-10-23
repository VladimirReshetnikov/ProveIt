import DiophantineConsistency.Bridge
import DiophantineConsistency.Polynomial

/-!
# Fixed polynomial representations of syntactic ZFC refutability

The semidecider in `Computability` is the concrete proof enumerator, not a
classical case distinction on consistency. The polynomial representations
are selected from proved MRDP/Jones existence theorems. Their coefficients
are not yet exported by an executable compiler.

The conclusions are external Lean theorems about the repository's syntactic
ZFC proof predicate. An object-language ZFC derivation is a further task.
-/

namespace DiophantineConsistency

open SetTheory LeanProofs.BoundedZFCConsistency

/-- One fixed integer polynomial in exactly nine natural witness slots. -/
noncomputable def zfcNinePolynomial : MvPolynomial (Fin 9) ℤ :=
  ninePolynomial (BProv ZFCax_s [] Form.fBot) zfcRefutationInputs_re

/-- Its natural zeros exist exactly when there is a finite ZFC refutation. -/
theorem zfcNinePolynomial_hasZero_iff_refutation :
    HasNaturalZero zfcNinePolynomial ↔ BProv ZFCax_s [] Form.fBot :=
  hasNaturalZero_ninePolynomial _ _

/-- Correctness of the nine-slot consistency representation. -/
theorem zfcNinePolynomial_noZero_iff_conZFC :
    (¬ HasNaturalZero zfcNinePolynomial) ↔ ConZFC :=
  not_congr zfcNinePolynomial_hasZero_iff_refutation

/-- A fixed polynomial with 58 natural witness slots and degree at most four. -/
noncomputable def zfcQuarticPolynomial : MvPolynomial (Fin 58) ℤ :=
  quarticPolynomial (BProv ZFCax_s [] Form.fBot) zfcRefutationInputs_re

theorem zfcQuarticPolynomial_degree_le_four :
    zfcQuarticPolynomial.totalDegree ≤ 4 :=
  totalDegree_quarticPolynomial_le_four _ _

theorem zfcQuarticPolynomial_hasZero_iff_refutation :
    HasNaturalZero zfcQuarticPolynomial ↔ BProv ZFCax_s [] Form.fBot :=
  hasNaturalZero_quarticPolynomial _ _

theorem zfcQuarticPolynomial_noZero_iff_conZFC :
    (¬ HasNaturalZero zfcQuarticPolynomial) ↔ ConZFC :=
  not_congr zfcQuarticPolynomial_hasZero_iff_refutation

/-- The two alternatives have equivalent solvability, without assuming Con(ZFC). -/
theorem nine_hasZero_iff_quartic_hasZero :
    HasNaturalZero zfcNinePolynomial ↔ HasNaturalZero zfcQuarticPolynomial :=
  zfcNinePolynomial_hasZero_iff_refutation.trans
    zfcQuarticPolynomial_hasZero_iff_refutation.symm

end DiophantineConsistency
