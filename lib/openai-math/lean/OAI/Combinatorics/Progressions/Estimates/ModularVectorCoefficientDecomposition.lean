import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.MvPolynomial.Basic

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {A B I R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [CommRing R]

noncomputable def designatedVectorComponent (S : B → A → Finset I)
    (Q : B → MvPolynomial I R) (c : B → A → R) (b : B) : MvPolynomial I R :=
  Q b + ∑ a, c b a • ∏ i ∈ S b a, X i

theorem designatedVectorComponent_update_row (S : B → A → Finset I)
    (Q : B → MvPolynomial I R) (w : B → R) (c : B → A → R)
    (b₀ : B) (d : A → R) :
    (∑ b, w b • designatedVectorComponent S Q (Function.update c b₀ d) b) =
      (∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b) +
        w b₀ • Q b₀ + ∑ a, (w b₀ * d a) • ∏ i ∈ S b₀ a, X i := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b₀)]
  have hrest : (∑ b ∈ Finset.univ.erase b₀,
      w b • designatedVectorComponent S Q (Function.update c b₀ d) b) =
      ∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [designatedVectorComponent, Function.update_of_ne (Finset.ne_of_mem_erase hb)]
  rw [hrest]
  simp only [designatedVectorComponent, Function.update_self, smul_add, Finset.smul_sum, smul_smul,
    add_assoc]

end Erdos3

end

end OAI
