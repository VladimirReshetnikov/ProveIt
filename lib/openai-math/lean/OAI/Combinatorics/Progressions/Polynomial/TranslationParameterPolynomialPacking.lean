import Mathlib.Algebra.MvPolynomial.Equiv

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommSemiring R]

noncomputable def packTranslationPolynomial :
    MvPolynomial B (MvPolynomial U R) ≃ₐ[R] MvPolynomial (U ⊕ B) R :=
  (commAlgEquiv R B U).trans (sumAlgEquiv R U B).symm

@[simp] theorem packTranslationPolynomial_X (i : B) :
    packTranslationPolynomial (R := R) (U := U) (X i) = X (Sum.inr i) := by
  simp [packTranslationPolynomial]

@[simp] theorem packTranslationPolynomial_C_X (i : U) :
    packTranslationPolynomial (R := R) (B := B) (C (X i)) = X (Sum.inl i) := by
  simp only [packTranslationPolynomial, AlgEquiv.trans_apply, commAlgEquiv_C_X,
    sumAlgEquiv_symm_X]

@[simp] theorem packTranslationPolynomial_C (P : MvPolynomial U R) :
    packTranslationPolynomial (B := B) (C P) = rename Sum.inl P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [packTranslationPolynomial]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, rename_X]
    rw [packTranslationPolynomial_C_X]

theorem coeff_packTranslationPolynomial (Q : MvPolynomial B (MvPolynomial U R))
    (α : U →₀ ℕ) (β : B →₀ ℕ) :
    (packTranslationPolynomial Q).coeff (α.sumElim β) = (Q.coeff β).coeff α := by
  classical
  simp only [packTranslationPolynomial, sumAlgEquiv, commAlgEquiv,
    AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply]
  change (AddMonoidAlgebra.domCongr R R
    (Finsupp.sumFinsuppAddEquivProdFinsupp.symm)
      ((AddMonoidAlgebra.curryAlgEquiv R).symm
        ((AddMonoidAlgebra.commAlgEquiv R) Q))).coeff (α.sumElim β) = _
  rw [AddMonoidAlgebra.coeff_domCongr]
  simp only [AddEquiv.symm_symm, Finsupp.sumFinsuppAddEquivProdFinsupp_apply,
    Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  change ((AddMonoidAlgebra.curryAlgEquiv R).symm
    ((AddMonoidAlgebra.commAlgEquiv R) Q)).coeff (α, β) = (Q.coeff β).coeff α
  rw [AddMonoidAlgebra.commAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, AddMonoidAlgebra.coeff_domCongr]
  rfl

theorem packTranslationPolynomial_specialize (u : U → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    aeval (Sum.elim (fun i => C (u i)) X) (packTranslationPolynomial Q) =
      MvPolynomial.map (eval u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C P =>
    rw [packTranslationPolynomial_C, map_C]
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP => simp only [map_mul, rename_X, aeval_X, Sum.elim_inl, eval_X, hP]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, packTranslationPolynomial_X, aeval_X,
      Sum.elim_inr, map_X, hP]

theorem packTranslationPolynomial_eval (u : U → R) (b : B → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    eval (Sum.elim u b) (packTranslationPolynomial Q) =
      eval b (MvPolynomial.map (eval u) Q) := by
  rw [← packTranslationPolynomial_specialize u Q]
  change (aeval (Sum.elim u b)) _ = (aeval b) ((aeval _) _)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  cases i <;> simp

end Erdos3

end

end OAI
