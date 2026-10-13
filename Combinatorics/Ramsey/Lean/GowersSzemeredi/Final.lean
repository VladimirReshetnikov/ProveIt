import GowersSzemeredi.Proofs18CoverPaddedFinal
import GowersSzemeredi.Proofs01QuantitativeHeadline

/-! Gowers's final quantitative theorem with its original bounds.

The proof uses the uniform cover argument at lengths at least six and takes
progression prefixes. The density and coloring consequences share this one
proof of Theorem 18.2.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.2**, with the printed threshold and positive-step natural
arithmetic progressions. -/
theorem theorem_18_2_explicit : theorem_18_2 := theorem_18_2_padded

/-- **Corollary 18.7**, by choosing a color class of density at least one half. -/
theorem corollary_18_7_explicit : corollary_18_7 :=
  corollary_18_7_holds_of_theorem_18_2 theorem_18_2_explicit

/-- **Theorem 1.2**, through Theorem 18.2. -/
theorem theorem_1_2_explicit : theorem_1_2 :=
  theorem_1_2_holds_of_theorem_18_2 theorem_18_2_explicit

/-- **Theorem 1.3**, through Theorem 18.2. -/
theorem theorem_1_3_explicit : theorem_1_3 :=
  theorem_1_3_holds_of_theorem_18_2 theorem_18_2_explicit

end LeanProofs.GowersSzemeredi
