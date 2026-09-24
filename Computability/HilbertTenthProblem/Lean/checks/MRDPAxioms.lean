import Diophantine.MRDP
import Diophantine.Common.PrimitiveRecursiveDioph

/-!
Audit the concise MRDP proof, its scalar and article adapters, and the converse.
The checked statements retain natural inputs and witnesses, including zero,
and choose a single finite integer polynomial before the input.
-/

#print axioms MRDP.binomial_diophFn
#print axioms MRDP.exists_fin_polynomial
#print axioms MRDP.factorial_diophFn
#print axioms MRDP.encodedModuliProduct_eq_prod
#print axioms MRDP.boundedForall_dioph
#print axioms MRDP.recursionTrace_iff
#print axioms MRDP.primrec_diophFn
#print axioms MRDP.mrdp
#print axioms Diophantine.natPrimrec_dioph_comp
#print axioms Diophantine.natPrimrec_dioph
#print axioms Diophantine.encoded_evaln_natPrimrec
#print axioms Diophantine.rePred_dioph
#print axioms Diophantine.dioph_iff_exists_fin_polynomial
#print axioms Diophantine.mrdp
#print axioms Diophantine.finite_polynomial_rePred
#print axioms Diophantine.dioph_rePred
#print axioms Diophantine.mrdp_dioph_iff
#print axioms Diophantine.mrdp_iff

-- Reject unexpected assumptions transitively, rather than only printing them.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``MRDP.binomial_diophFn, ``MRDP.exists_fin_polynomial,
    ``MRDP.factorial_diophFn, ``MRDP.encodedModuliProduct_eq_prod,
    ``MRDP.boundedForall_dioph, ``MRDP.recursionTrace_iff,
    ``MRDP.primrec_diophFn, ``MRDP.mrdp,
    ``Diophantine.natPrimrec_dioph_comp, ``Diophantine.natPrimrec_dioph,
    ``Diophantine.encoded_evaln_natPrimrec, ``Diophantine.rePred_dioph,
    ``Diophantine.dioph_iff_exists_fin_polynomial, ``Diophantine.mrdp,
    ``Diophantine.finite_polynomial_rePred, ``Diophantine.dioph_rePred,
    ``Diophantine.mrdp_dioph_iff, ``Diophantine.mrdp_iff]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {declaration}: {axiomName}"

-- Restate the public contracts independently, without opening namespaces or
-- using the proof's abbreviations, to catch accidental statement weakening.
example : ∀ {S : Set ℕ}, REPred S →
    ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n : ℕ, n ∈ S ↔ ∃ w : Fin k → ℕ,
        MvPolynomial.eval
          (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P = 0 :=
  @Diophantine.mrdp

example : ∀ {S : Set ℕ}, REPred S ↔
    ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n : ℕ, n ∈ S ↔ ∃ w : Fin k → ℕ,
        MvPolynomial.eval
          (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P = 0 :=
  @Diophantine.mrdp_iff

example : ∀ {S : Set ℕ}, REPred S ↔ Dioph {v : Unit → ℕ | v () ∈ S} :=
  @Diophantine.mrdp_dioph_iff
