import AperiodicMonotile.Periodicity
import IPRADerivations.Core.Parity
import IPRADerivations.Core.DescentEx
import IPRADerivations.Core.Pigeonhole
import IPRADerivations.Core.Pairing
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-theory target

The ordinary set-theoretic assertion "there exists an infinite tiling" is not itself a
first-order arithmetic formula.  The internal theorem uses a primitive-recursive coherent
stream of finite observations and the finite-torus negation of periodicity.
-/

namespace AperiodicMonotile.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Object-language symbols for the closed certificate checker and patch generator. -/
opaque validHatPatchF : PR 2
opaque coversF : PR 3
opaque patchF : PR 1
opaque periodicTorusF : PR 1

abbrev validHatPatch (n r : PTm k) : PTm k := ap2 validHatPatchF n r
abbrev covers (n r : PTm k) : PTm k := ap2 (comp _ coversF ![var 0, var 1, zero]) n r
abbrev periodicTorus (c : PTm k) : PTm k := ap1 periodicTorusF c

/-- For every radius r, the canonical finite observation is a valid cover. -/
opaque tilabilitySentence : Fm PTm 0
/-- Every finite torus code fails the periodic-hat checker. -/
opaque aperiodicitySentence : Fm PTm 0

abbrev einsteinHatSentence : Fm PTm 0 := tilabilitySentence ⋏ aperiodicitySentence

/-- Reification of the exact affine and combinatorial certificate. -/
theorem tilability_derivation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] tilabilitySentence := by
  /-
  * define the generator with `Core/Definitions` and simultaneous recursion;
  * reflect each closed affine identity by `deriveNat`/`ipra_ring`;
  * use quantifier-free induction on the substitution level;
  * instantiate the radius-growth bound and introduce the existential witness.
  -/
  sorry

/-- Reification of the finite-torus coupling and descent. -/
theorem aperiodicity_derivation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] aperiodicitySentence := by
  /-
  * decode a candidate torus with `Core/Pairing` and bounded search;
  * derive alignment and the three strip-cycle witnesses by bounded recursion;
  * reduce the determinant and similarity equations with `ipra_ring`;
  * invoke the object-theory 2-adic descent, built from `Core/Parity` and
    `Core/DescentEx`.
  -/
  sorry

/-- The requested iPRA theorem. -/
theorem einstein_hat_ipra :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] einsteinHatSentence :=
  Prf.andI tilability_derivation aperiodicity_derivation

/-- Transfer to the checked native scalar core.  Fill the exact theorem name/type from
    `ConciseIPRA.NativeBiInterpretation` after the object formula is fixed. -/
opaque einstein_hat_native : True

end AperiodicMonotile.IPRA
