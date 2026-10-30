import ZFCinPA.SizedDriverAtoms
import ZFCinPA.SizedDriverConn
import ZFCinPA.SizedDriverQuant

/-!
# The bounded `hSchema` driver

`LDriver.driver` proves, by the `Σ₁` structural induction on semiformula
codes, that for every internal formula `p` of level `n` some function code `f`
makes the reflection invariant of `envForm n p` an internal `𝗭𝗙` theorem. This
module proves the bounded twin `driver_le`: for a target `M` and every
`n + p ≤ M`, the function code is at level

`Gd M p = Ad M · 2^(Kd · p)`,

and the invariant is derived within `Wd M + 60 + 40 p` on the `DLv` scale.

**Levels.** Every predicate placeholder is an environment transform
`envForm n q` with `n + q ≤ M`, at level `A0 M` (`SizedEnvForm.envForm_le`).
A function code of a compound formula is a translation of a fixed body at the
codes of its parts, which multiplies the level by `tB`. `Gd` absorbs this
because `2^Kd ≥ 2 tB + 2` (`Gd_grow`). All placeholders are at level
`uD M = Gd M M`, so every step compiles at the one level `uD M`
(`SizedDriverSteps`), and each step adds `30` derivation levels.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriver

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le verum_le)
open LeanProofs.ZFCinPA.SizedLNumOK LeanProofs.ZFCinPA.SizedDriverSteps
open LeanProofs.ZFCinPA.SizedEnvForm (Eb Ef0 envForm_le atomOf_le idx_le falsum_le)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LDriver
open LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_val)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

/-- **The bounded driver.** For a target `M` and every semiformula `p` of level
`n` with `n + p ≤ M`, a function code at level `Gd M p` makes the reflection
invariant of `envForm n p` derivable within `Wd M + 60 + 40 p`. -/
theorem driver_le {M n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (hM : n + p ≤ M) :
    ∃ F : SF V 2, F.val ≤ lvB (Gd M p) ∧
      DLv 𝗭𝗙 (insert (InvT (envFormT n hp) F).val ∅) (Wd M + 60 + 40 * p) := by
  have key : ΘB (Ad M) Kd (Wd M + 60) M n p :=
    IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ) (P := ΘB (Ad M) Kd (Wd M + 60) M)
      (ΘB_definable _ _ _ _) (case_atom false M) (case_atom true M) (case_verum M) (case_falsum M)
      (case_and M) (case_or M) (case_all M) (case_exs M) hp
  exact typed_of_ΘB hp (key hM)

end LeanProofs.ZFCinPA.SizedDriver
