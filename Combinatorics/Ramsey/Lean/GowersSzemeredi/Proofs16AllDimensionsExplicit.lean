import GowersSzemeredi.Proofs16AllDimensions
import GowersSzemeredi.Proofs16ExplicitRecurrenceProfiles
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58
import GowersSzemeredi.Proofs16AllDimensionsSide

/-! **Theorem 16.2 and Corollary 16.11, unconditionally, in every dimension.**

This module is a bridge. `theorem_16_2_of_profiles_all` (light, kernel-checked
locally) needs:
* the recurrence profiles in every dimension `k ≥ 1`. These come from
  `section16RecurrenceProfileWith_explicit k`, at
  `Kc k = ⌈multiaffinePartitionK (k+1) (2^(k+1))⌉` and
  `pc k = (k+1)·multiaffinePartitionP (k+1) (2^(k+1))`;
* the bound `Kc k + pc k ≤ 2^(2^(2^(k+5)))` (`explicit_family_constants_le`).

The constant bound follows the Schmidt layer down to the Weyl budget:
* `schmidtWeylD_le_gen` and `schmidtWeylC_le_gen` come from the light bounds
  on `weylBudgetPolynomial` in every degree;
* `schmidtMonomialK_le_gen` uses the symbolic Schmidt formula
  `schmidt_base_formula_le_gen`; `schmidtMonomialP_le_gen` is direct;
* `uniformSchmidtK_le_of`, `uniformSchmidtP_le_of`,
  `multiaffinePartitionK_le_of` and `multiaffinePartitionP_le_pow` give the
  partition constants, and `family_constants_tower_le` closes the
  arithmetic.

The imports reach the port's Schmidt constants and the explicit profiles, so
this module is checked on the full-verification host. Every step is a
definitional unfolding or an instantiation of a kernel-checked statement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 16.2 and Corollary 16.11 in every dimension.** -/
theorem theorem_16_2_and_corollary_16_11 : theorem_16_2 ∧ corollary_16_11 :=
  theorem_16_2_of_profiles_all
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k)

/-- **Theorem 16.2.** -/
theorem theorem_16_2_explicit : theorem_16_2 := theorem_16_2_and_corollary_16_11.1

/-- **Corollary 16.11.** -/
theorem corollary_16_11_explicit : corollary_16_11 := theorem_16_2_and_corollary_16_11.2

end LeanProofs.GowersSzemeredi
