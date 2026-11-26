import IPRADerivations.Foundations.TraceReflection
import IPRADerivations.Core.Descent
import IPRADerivations.Core.Header

/-!
# Composition of extensional contracts

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`,
`ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16` (Theorem "Extensional contract
composition"); the same statement is `thm:precision-composition` of
`ipra_certified_finitary_framework_2026-11-15` ("If `F` is extensional with demand `D_F` and `G` is extensional
with demand `D_G`, then `G ∘ F` is extensional with demand `D_F ∘ D_G`").

Precision-indexed equivalences are arbitrary formulas `EX(q, c, c')`, `EY(q, y, y')`, `EZ(r, z, z')`
("`c ≈_q c'`"); the maps `C : X → Y`, `D : Y → Z` and the demands `d_C`, `d_D` are unary terms. The
congruence moduli are closed derivations

`EX(d_C(q), c, c') → EY(q, C(c), C(c'))`,   `EY(d_D(r), y, y') → EZ(r, D(y), D(y'))`

with `q, c, c'` free.

* `ext_compose`: then `EX(d_C(d_D(r)), c, c') → EZ(r, D(C(c)), D(C(c')))` is derivable with `r, c, c'` free:
  the composite `D ∘ C` has demand `d_C ∘ d_D`;
* `ext_compose_closed`: the same as a closed sentence.

No property of the equivalences is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ExtensionalComposition

open_ipra
open LeanProofs.IPRA.Foundations.TraceReflection (I3 subst_I3)

variable {EX EY EZ : Fm PTm 3} {C D dC dD : PTm 1}

/-- The composite of two extensional maps is extensional, with the composed demand. Variables: `0 = r`,
`1 = c`, `2 = c'`. -/
theorem ext_compose
    (hC : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      I3 EX (inst1 dC (var 0)) (var 1) (var 2) ⟶ I3 EY (var 0) (inst1 C (var 1)) (inst1 C (var 2)))
    (hD : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      I3 EY (inst1 dD (var 0)) (var 1) (var 2) ⟶ I3 EZ (var 0) (inst1 D (var 1)) (inst1 D (var 2))) :
    ([] : List (Fm PTm 3)) ⊢[PRAAx]
      I3 EX (inst1 dC (inst1 dD (var 0))) (var 1) (var 2) ⟶
        I3 EZ (var 0) (inst1 D (inst1 C (var 1))) (inst1 D (inst1 C (var 2))) := by
  refine .impI ?_
  have a := inst (Γ := [I3 EX (inst1 dC (inst1 dD (var 0))) (var 1) (var 2)]) hC
    (![inst1 dD (var 0), var 1, var 2] : Fin 3 → PTm 3)
  simp only [Fm.subst_imp, subst_I3, subst_inst1, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at a
  have b := inst (Γ := [I3 EX (inst1 dC (inst1 dD (var 0))) (var 1) (var 2)]) hD
    (![var 0, inst1 C (var 1), inst1 C (var 2)] : Fin 3 → PTm 3)
  simp only [Fm.subst_imp, subst_I3, subst_inst1, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at b
  exact Prf.impE b (Prf.impE a Prf.hyp0)

/-- The closed sentence over `r`, `c`, `c'`. -/
theorem ext_compose_closed
    (hC : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      I3 EX (inst1 dC (var 0)) (var 1) (var 2) ⟶ I3 EY (var 0) (inst1 C (var 1)) (inst1 C (var 2)))
    (hD : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      I3 EY (inst1 dD (var 0)) (var 1) (var 2) ⟶ I3 EZ (var 0) (inst1 D (var 1)) (inst1 D (var 2))) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (I3 EX (inst1 dC (inst1 dD (var 0))) (var 1) (var 2) ⟶
        I3 EZ (var 0) (inst1 D (inst1 C (var 1))) (inst1 D (inst1 C (var 2)))) :=
  closeUniv 3 (ext_compose hC hD)

end LeanProofs.IPRA.Foundations.ExtensionalComposition
