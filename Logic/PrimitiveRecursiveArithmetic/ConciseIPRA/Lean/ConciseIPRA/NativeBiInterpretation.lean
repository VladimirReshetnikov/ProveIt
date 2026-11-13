import ConciseIPRA.NativeRoundTrip
import ConciseIPRA.BiInterpretation

/-!
# Bi-interpretability of the native scalar core with iPRA

The native scalar core (formulas `s = t`, `Q`, `D`; no connectives) is
bi-interpretable with intuitionistic primitive recursive arithmetic:

* `NFm.toPRA` reads a native formula as a formula of iPRA, and `NFm.ofPRA`
  reads a formula of iPRA as a native formula;
* both readings are faithful (`native_iff_pra`, `pra_iff_native`);
* both round trips are the identity up to provable equivalence
  (`native_roundTrip`, `pra_native_roundTrip`);
* the two systems are equiconsistent (`native_inconsistent_iff`).

The proof composes the native-to-`T_eq` bridge of this library with the
synonymy `biInterp` of `T_eq` and iPRA.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n : ℕ}

/-- The ordinary reading of a native formula in the language of iPRA. -/
def NFm.toPRA (A : NFm n) : Fm PTm n := A.toFm.map fun _ => ToPRA.tau

/-- The native reading of a formula of iPRA. -/
def NFm.ofPRA (φ : Fm PTm n) : NFm n := NFm.ofFm (φ.map fun _ => FromPRA.sigma)

/-- The native calculus proves a sequent exactly when iPRA proves its reading. -/
theorem native_iff_pra {Γ : List (NFm n)} {A : NFm n} :
    NPrf Γ A ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) := by
  rw [NPrf.iff_teq, teq_iff_pra, List.map_map]
  rfl

/-- iPRA proves a sequent exactly when the native calculus proves its reading. -/
theorem pra_iff_native {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔ NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) := by
  rw [pra_iff_teq, Teq.iff_native, List.map_map]
  rfl

/-- The native round trip through iPRA is the identity up to interderivability. -/
theorem native_roundTrip (A : NFm n) : NEquiv (NFm.ofPRA A.toPRA) A := by
  have h₁ : NPrf [NFm.ofFm A.toFm] (NFm.ofPRA A.toPRA) :=
    NPrf.ofPrf (Prf.iffMp (teq_roundTrip A.toFm [A.toFm]) Prf.hyp0)
  have h₂ : NPrf [NFm.ofPRA A.toPRA] (NFm.ofFm A.toFm) :=
    NPrf.ofPrf (Prf.iffMpr
      (teq_roundTrip A.toFm [(A.toFm.map fun _ => ToPRA.tau).map fun _ => FromPRA.sigma])
      Prf.hyp0)
  exact (NEquiv.symm ⟨h₁, h₂⟩).trans (NEquiv.ofFm_toFm A)

/-- In iPRA, every formula is equivalent to the reading of its native reading. -/
theorem pra_native_roundTrip (φ : Fm PTm n) (Γ : List (Fm PTm n)) :
    Γ ⊢[PRAAx] Fm.iff φ (NFm.ofPRA φ).toPRA := by
  have h₂ : Γ ⊢[PRAAx] Fm.iff ((φ.map fun _ => FromPRA.sigma).map fun _ => ToPRA.tau)
      (NFm.ofPRA φ).toPRA :=
    (biInterp.F.sound (Teq.iff_toFm_ofFm (φ.map fun _ => FromPRA.sigma) (Γ := []))).ofNil
  exact Prf.iffTrans (pra_roundTrip φ Γ) h₂

/-- The native calculus and iPRA are equiconsistent. -/
theorem native_inconsistent_iff :
    NPrf ([] : List (NFm 0)) NFm.bot ↔ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) :=
  (Teq.iff_native (Γ := []) (φ := Fm.bot)).symm.trans teq_consistent_iff

end LeanProofs.ConciseIPRA
